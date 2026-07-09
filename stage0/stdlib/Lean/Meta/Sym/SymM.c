// Lean compiler output
// Module: Lean.Meta.Sym.SymM
// Imports: public import Lean.Meta.Sym.AlphaShareCommon public import Lean.Meta.CongrTheorems public import Lean.Meta.Transform import Lean.Meta.WHNF import Lean.Meta.AppBuilder
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Sym_isUnfoldReducibleCandidate(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_isProj___boxed(lean_object*);
lean_object* l_Lean_getStructureInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_mkProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initializing();
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqI(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sym"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(230, 3, 132, 38, 134, 149, 222, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 1, 190, 45, 30, 82, 81, 176)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "check invariants"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(254, 148, 146, 121, 82, 137, 202, 245)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(81, 198, 26, 180, 162, 99, 75, 86)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_sym_debug;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "issues"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(230, 3, 132, 38, 134, 149, 222, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 90, 109, 68, 195, 255, 174, 185)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(215, 84, 158, 71, 120, 158, 242, 63)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "SymM"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(62, 120, 93, 45, 98, 183, 49, 234)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__9_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(135, 107, 0, 166, 43, 148, 190, 162)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__9_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__9_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__10_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__9_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(250, 253, 133, 58, 166, 2, 152, 17)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__10_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__10_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__11_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__10_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(254, 230, 149, 24, 177, 0, 168, 74)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__11_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__11_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__12_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__11_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(247, 70, 210, 197, 64, 19, 25, 35)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__12_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__12_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__13_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__13_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__13_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__14_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__12_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__13_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 119, 254, 183, 253, 57, 73, 33)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__14_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__14_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__15_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__15_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__15_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__16_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__14_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__15_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(247, 29, 178, 129, 13, 184, 131, 91)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__16_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__16_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__17_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__16_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(138, 150, 153, 124, 1, 171, 141, 81)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__17_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__17_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__18_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__17_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(46, 97, 109, 246, 28, 99, 14, 68)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__18_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__18_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__19_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__18_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(231, 39, 117, 214, 12, 215, 126, 174)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__19_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__19_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__20_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__19_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(46, 149, 253, 44, 239, 131, 52, 47)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__20_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__20_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__22_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__22_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__22_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__24_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__24_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__24_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2____boxed(lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_SymExtensionStateSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_SymExtensionStateSpec___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_SymExtensionStateSpec___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_SymExtensionStateSpec = (const lean_object*)&l_Lean_Meta_Sym_SymExtensionStateSpec___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtensionState;
static const lean_string_object l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0();
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0_value)}};
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default(lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymExtension___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension(lean_object*);
static const lean_array_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_registerSymExtension___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 92, .m_capacity = 92, .m_length = 91, .m_data = "failed to register `Sym` extension, extensions can only be registered during initialization"};
static const lean_object* l_Lean_Meta_Sym_registerSymExtension___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_registerSymExtension___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtensions_mkInitialStates___boxed(lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instInhabitedProofInstArgInfo = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0_value;
static const lean_array_object l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instInhabitedProofInstInfo_default = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instInhabitedProofInstInfo = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_none_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_none_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_interlaced_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_interlaced_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_instInhabitedConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_instInhabitedConfig_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instInhabitedConfig_default = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instInhabitedConfig = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedConfig_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_unfoldReducibleStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_unfoldReducibleStep___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_unfoldReducibleStep___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducibleStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducibleStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_unfoldReducible___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_unfoldReducible___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_unfoldReducible___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_unfoldReducible___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_unfoldReducible___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_unfoldReducibleStep___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_unfoldReducible___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_unfoldReducible___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_foldProjs___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__2;
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "found `Expr.proj` with invalid field index `"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__4;
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__6;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Sym_foldProjs___lam__0___closed__7;
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "found `Expr.proj` but `"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__9;
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` is not marked as structure"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_foldProjs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_isProj___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_foldProjs___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_foldProjs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_foldProjs___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_foldProjs___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___closed__1_value;
static const lean_closure_object l_Lean_Meta_Sym_foldProjs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_foldProjs___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_foldProjs___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__3_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__7_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__10 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__10_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Ordering"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__14 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "eq"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__15 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__14_value),LEAN_SCALAR_PTR_LITERAL(226, 44, 125, 228, 251, 150, 72, 72)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__15_value),LEAN_SCALAR_PTR_LITERAL(103, 150, 86, 2, 28, 163, 164, 77)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1(lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_SymM_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Sym_SymM_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__2;
static lean_once_cell_t l_Lean_Meta_Sym_SymM_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__3;
static const lean_string_object l_Lean_Meta_Sym_SymM_run___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Meta.Sym.SymM"};
static const lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_SymM_run___redArg___closed__4_value;
static const lean_string_object l_Lean_Meta_Sym_SymM_run___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Sym.SymM.run"};
static const lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_SymM_run___redArg___closed__5_value;
static const lean_string_object l_Lean_Meta_Sym_SymM_run___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_SymM_run___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Sym_SymM_run___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.Meta.Sym.shareCommonWithoutChecks"};
static const lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "internal error, expression has loose bound variables at `shareCommon`"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_reportIssue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "issue"};
static const lean_object* l_Lean_Meta_Sym_reportIssue___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_reportIssue___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_reportIssue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_reportIssue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 190, 118, 187, 186, 110, 108, 236)}};
static const lean_object* l_Lean_Meta_Sym_reportIssue___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_reportIssue___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_reportIssue___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_reportIssue___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__4_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Sym.reportIssueIfVerbose"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "reportIssueIfVerbose"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(118, 254, 137, 8, 139, 198, 210, 169)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__8_value),LEAN_SCALAR_PTR_LITERAL(82, 43, 55, 72, 125, 82, 73, 158)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 165, 116, 130, 189, 215, 142, 41)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__11 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__13 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "interpolatedStrKind"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__15 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__15_value),LEAN_SCALAR_PTR_LITERAL(239, 118, 32, 248, 73, 51, 110, 198)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__17 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__17_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__19 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__19_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__22 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__22_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__26 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__26_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MessageData"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29_value),LEAN_SCALAR_PTR_LITERAL(117, 193, 162, 252, 67, 31, 191, 159)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29_value),LEAN_SCALAR_PTR_LITERAL(204, 233, 154, 112, 39, 152, 210, 6)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__33 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__33_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32_value)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__34 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__34_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__34_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__35 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__35_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__33_value),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__35_value)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termM!_"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__38 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__38_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__38_value),LEAN_SCALAR_PTR_LITERAL(241, 254, 249, 246, 41, 222, 210, 184)}};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39_value;
static const lean_string_object l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "m!"};
static const lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40 = (const lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "doElemReportIssue!__"};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__0 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 149, 154, 203, 214, 83, 169, 43)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__2 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__3 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reportIssue!"};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__4 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__4_value)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__5 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__5_value;
static const lean_string_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__6 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__7 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__7_value;
static const lean_string_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "interpolatedStr"};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__8 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__8_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(156, 58, 177, 246, 99, 11, 16, 252)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__9 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__9_value;
static const lean_string_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__10 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__10_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__11 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__11_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__12 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__12_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__9_value),((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__12_value)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__13 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__13_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__7_value),((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__13_value),((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__12_value)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__14 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__14_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__3_value),((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__5_value),((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__14_value)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__15 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__15_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__15_value)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__16 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__16_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_doElemReportIssue_x21____ = (const lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Sym.reportDbgIssue"};
static const lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1;
static const lean_string_object l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "reportDbgIssue"};
static const lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(118, 254, 137, 8, 139, 198, 210, 169)}};
static const lean_ctor_object l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(100, 136, 27, 81, 109, 98, 120, 61)}};
static const lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(37, 182, 25, 82, 56, 230, 186, 254)}};
static const lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "doElemReportDbgIssue!__"};
static const lean_object* l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__0 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 81, 179, 30, 51, 192, 195, 77)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "reportDbgIssue!"};
static const lean_object* l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__2 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__2_value)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__3 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__3_value),((lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__3_value),((lean_object*)&l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__14_value)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__4 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__4_value)}};
static const lean_object* l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__5 = (const lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_doElemReportDbgIssue_x21____ = (const lean_object*)&l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__1;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__2;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__3;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__4;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__5;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__6;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__7;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__8;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__9;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__10;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__11;
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymM___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__12 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___closed__12_value;
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymM___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__13 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___closed__13_value;
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymM___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__14 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___closed__14_value;
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymM___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__15 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___closed__15_value;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__16;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__17;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__18;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__19;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__20;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__21;
static const lean_string_object l_Lean_Meta_Sym_instInhabitedSymM___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "<SymM default value>"};
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__22 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___closed__22_value;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__23;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_55_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_));
v___x_56_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_));
v___x_57_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_));
v___x_58_ = l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0(v___x_55_, v___x_56_, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4____boxed(lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_();
return v_res_60_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_114_ = lean_unsigned_to_nat(2410647589u);
v___x_115_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__20_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_116_ = l_Lean_Name_num___override(v___x_115_, v___x_114_);
return v___x_116_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_118_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__22_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_119_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_);
v___x_120_ = l_Lean_Name_str___override(v___x_119_, v___x_118_);
return v___x_120_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__24_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_123_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_);
v___x_124_ = l_Lean_Name_str___override(v___x_123_, v___x_122_);
return v___x_124_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = lean_unsigned_to_nat(2u);
v___x_126_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_);
v___x_127_ = l_Lean_Name_num___override(v___x_126_, v___x_125_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_129_; uint8_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_129_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_130_ = 0;
v___x_131_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_);
v___x_132_ = l_Lean_registerTraceClass(v___x_129_, v___x_130_, v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2____boxed(lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_();
return v_res_134_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymExtensionState(void){
_start:
{
lean_object* v___x_138_; lean_object* v_snd_139_; 
v___x_138_ = ((lean_object*)(l_Lean_Meta_Sym_SymExtensionStateSpec));
v_snd_139_ = lean_ctor_get(v___x_138_, 1);
lean_inc(v_snd_139_);
return v_snd_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0(){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__1));
v___x_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___boxed(lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0();
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default(lean_object* v_00_u03c3_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__1));
return v___x_153_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymExtension___closed__0(void){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_Meta_Sym_instInhabitedSymExtension_default(lean_box(0));
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension(lean_object* v_a_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymExtension___closed__0, &l_Lean_Meta_Sym_instInhabitedSymExtension___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymExtension___closed__0);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_));
v___x_161_ = lean_st_mk_ref(v___x_160_);
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2____boxed(lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_();
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg(lean_object* v_ext_165_){
_start:
{
lean_inc_ref(v_ext_165_);
return v_ext_165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg___boxed(lean_object* v_ext_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg(v_ext_166_);
lean_dec_ref(v_ext_166_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1(lean_object* v_00_u03c3_168_, lean_object* v_ext_169_){
_start:
{
lean_inc_ref(v_ext_169_);
return v_ext_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___boxed(lean_object* v_00_u03c3_170_, lean_object* v_ext_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1(v_00_u03c3_170_, v_ext_171_);
lean_dec_ref(v_ext_171_);
return v_res_172_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = ((lean_object*)(l_Lean_Meta_Sym_registerSymExtension___redArg___closed__0));
v___x_175_ = lean_mk_io_user_error(v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension___redArg(lean_object* v_mkInitial_176_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_initializing();
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_198_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_198_ == 0)
{
v___x_181_ = v___x_178_;
v_isShared_182_ = v_isSharedCheck_198_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_198_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
uint8_t v___x_183_; 
v___x_183_ = lean_unbox(v_a_179_);
lean_dec(v_a_179_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; lean_object* v___x_186_; 
lean_dec_ref(v_mkInitial_176_);
v___x_184_ = lean_obj_once(&l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1, &l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1_once, _init_l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1);
if (v_isShared_182_ == 0)
{
lean_ctor_set_tag(v___x_181_, 1);
lean_ctor_set(v___x_181_, 0, v___x_184_);
v___x_186_ = v___x_181_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
else
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_188_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef;
v___x_189_ = lean_st_ref_get(v___x_188_);
v___x_190_ = lean_st_ref_take(v___x_188_);
v___x_191_ = lean_array_get_size(v___x_189_);
lean_dec(v___x_189_);
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v_mkInitial_176_);
lean_inc_ref(v___x_192_);
v___x_193_ = lean_array_push(v___x_190_, v___x_192_);
v___x_194_ = lean_st_ref_set(v___x_188_, v___x_193_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_192_);
v___x_196_ = v___x_181_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_192_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_dec_ref(v_mkInitial_176_);
v_a_199_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_178_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_178_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension___redArg___boxed(lean_object* v_mkInitial_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Meta_Sym_registerSymExtension___redArg(v_mkInitial_207_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension(lean_object* v_00_u03c3_210_, lean_object* v_mkInitial_211_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_Meta_Sym_registerSymExtension___redArg(v_mkInitial_211_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension___boxed(lean_object* v_00_u03c3_214_, lean_object* v_mkInitial_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_Meta_Sym_registerSymExtension(v_00_u03c3_214_, v_mkInitial_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(size_t v_sz_218_, size_t v_i_219_, lean_object* v_bs_220_){
_start:
{
uint8_t v___x_222_; 
v___x_222_ = lean_usize_dec_lt(v_i_219_, v_sz_218_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; 
v___x_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_223_, 0, v_bs_220_);
return v___x_223_;
}
else
{
lean_object* v_v_224_; lean_object* v_mkInitial_225_; lean_object* v___x_226_; 
v_v_224_ = lean_array_uget_borrowed(v_bs_220_, v_i_219_);
v_mkInitial_225_ = lean_ctor_get(v_v_224_, 1);
lean_inc_ref(v_mkInitial_225_);
v___x_226_ = lean_apply_1(v_mkInitial_225_, lean_box(0));
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v___x_228_; lean_object* v_bs_x27_229_; size_t v___x_230_; size_t v___x_231_; lean_object* v___x_232_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref_known(v___x_226_, 1);
v___x_228_ = lean_unsigned_to_nat(0u);
v_bs_x27_229_ = lean_array_uset(v_bs_220_, v_i_219_, v___x_228_);
v___x_230_ = ((size_t)1ULL);
v___x_231_ = lean_usize_add(v_i_219_, v___x_230_);
v___x_232_ = lean_array_uset(v_bs_x27_229_, v_i_219_, v_a_227_);
v_i_219_ = v___x_231_;
v_bs_220_ = v___x_232_;
goto _start;
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
lean_dec_ref(v_bs_220_);
v_a_234_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_226_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_226_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0___boxed(lean_object* v_sz_242_, lean_object* v_i_243_, lean_object* v_bs_244_, lean_object* v___y_245_){
_start:
{
size_t v_sz_boxed_246_; size_t v_i_boxed_247_; lean_object* v_res_248_; 
v_sz_boxed_246_ = lean_unbox_usize(v_sz_242_);
lean_dec(v_sz_242_);
v_i_boxed_247_ = lean_unbox_usize(v_i_243_);
lean_dec(v_i_243_);
v_res_248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(v_sz_boxed_246_, v_i_boxed_247_, v_bs_244_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtensions_mkInitialStates(){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; size_t v_sz_252_; size_t v___x_253_; lean_object* v___x_254_; 
v___x_250_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef;
v___x_251_ = lean_st_ref_get(v___x_250_);
v_sz_252_ = lean_array_size(v___x_251_);
v___x_253_ = ((size_t)0ULL);
v___x_254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(v_sz_252_, v___x_253_, v___x_251_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtensions_mkInitialStates___boxed(lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx(lean_object* v_x_265_){
_start:
{
switch(lean_obj_tag(v_x_265_))
{
case 0:
{
lean_object* v___x_266_; 
v___x_266_ = lean_unsigned_to_nat(0u);
return v___x_266_;
}
case 1:
{
lean_object* v___x_267_; 
v___x_267_ = lean_unsigned_to_nat(1u);
return v___x_267_;
}
case 2:
{
lean_object* v___x_268_; 
v___x_268_ = lean_unsigned_to_nat(2u);
return v___x_268_;
}
default: 
{
lean_object* v___x_269_; 
v___x_269_ = lean_unsigned_to_nat(3u);
return v___x_269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx___boxed(lean_object* v_x_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_Meta_Sym_CongrInfo_ctorIdx(v_x_270_);
lean_dec(v_x_270_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(lean_object* v_t_272_, lean_object* v_k_273_){
_start:
{
switch(lean_obj_tag(v_t_272_))
{
case 0:
{
return v_k_273_;
}
case 1:
{
lean_object* v_prefixSize_274_; lean_object* v_suffixSize_275_; lean_object* v___x_276_; 
v_prefixSize_274_ = lean_ctor_get(v_t_272_, 0);
lean_inc(v_prefixSize_274_);
v_suffixSize_275_ = lean_ctor_get(v_t_272_, 1);
lean_inc(v_suffixSize_275_);
lean_dec_ref_known(v_t_272_, 2);
v___x_276_ = lean_apply_2(v_k_273_, v_prefixSize_274_, v_suffixSize_275_);
return v___x_276_;
}
default: 
{
lean_object* v_rewritable_277_; lean_object* v___x_278_; 
v_rewritable_277_ = lean_ctor_get(v_t_272_, 0);
lean_inc_ref(v_rewritable_277_);
lean_dec(v_t_272_);
v___x_278_ = lean_apply_1(v_k_273_, v_rewritable_277_);
return v___x_278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim(lean_object* v_motive_279_, lean_object* v_ctorIdx_280_, lean_object* v_t_281_, lean_object* v_h_282_, lean_object* v_k_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_281_, v_k_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim___boxed(lean_object* v_motive_285_, lean_object* v_ctorIdx_286_, lean_object* v_t_287_, lean_object* v_h_288_, lean_object* v_k_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Meta_Sym_CongrInfo_ctorElim(v_motive_285_, v_ctorIdx_286_, v_t_287_, v_h_288_, v_k_289_);
lean_dec(v_ctorIdx_286_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_none_elim___redArg(lean_object* v_t_291_, lean_object* v_none_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_291_, v_none_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_none_elim(lean_object* v_motive_294_, lean_object* v_t_295_, lean_object* v_h_296_, lean_object* v_none_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_295_, v_none_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim___redArg(lean_object* v_t_299_, lean_object* v_fixedPrefix_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_299_, v_fixedPrefix_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim(lean_object* v_motive_302_, lean_object* v_t_303_, lean_object* v_h_304_, lean_object* v_fixedPrefix_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_303_, v_fixedPrefix_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_interlaced_elim___redArg(lean_object* v_t_307_, lean_object* v_interlaced_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_307_, v_interlaced_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_interlaced_elim(lean_object* v_motive_310_, lean_object* v_t_311_, lean_object* v_h_312_, lean_object* v_interlaced_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_311_, v_interlaced_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim___redArg(lean_object* v_t_315_, lean_object* v_congrTheorem_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_315_, v_congrTheorem_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim(lean_object* v_motive_318_, lean_object* v_t_319_, lean_object* v_h_320_, lean_object* v_congrTheorem_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_319_, v_congrTheorem_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducibleStep(lean_object* v_e_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_Expr_getAppFn(v_e_329_);
if (lean_obj_tag(v___x_335_) == 4)
{
lean_object* v_declName_336_; lean_object* v___x_337_; lean_object* v_env_338_; uint8_t v___x_339_; 
v_declName_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_declName_336_);
lean_dec_ref_known(v___x_335_, 2);
v___x_337_ = lean_st_ref_get(v_a_333_);
v_env_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc_ref(v_env_338_);
lean_dec(v___x_337_);
v___x_339_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_338_, v_declName_336_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; 
lean_dec_ref(v_e_329_);
v___x_340_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
return v___x_341_;
}
else
{
uint8_t v___x_342_; lean_object* v___x_343_; 
v___x_342_ = 0;
v___x_343_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_329_, v___x_342_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_363_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_363_ == 0)
{
v___x_346_ = v___x_343_;
v_isShared_347_ = v_isSharedCheck_363_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_343_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_363_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
if (lean_obj_tag(v_a_344_) == 1)
{
lean_object* v_val_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_358_; 
v_val_348_ = lean_ctor_get(v_a_344_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v_a_344_);
if (v_isSharedCheck_358_ == 0)
{
v___x_350_ = v_a_344_;
v_isShared_351_ = v_isSharedCheck_358_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_val_348_);
lean_dec(v_a_344_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_358_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_val_348_);
v___x_353_ = v_reuseFailAlloc_357_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_355_; 
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_353_);
v___x_355_ = v___x_346_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
else
{
lean_object* v___x_359_; lean_object* v___x_361_; 
lean_dec(v_a_344_);
v___x_359_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_359_);
v___x_361_ = v___x_346_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
else
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
v_a_364_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_343_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_343_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
else
{
lean_object* v___x_372_; lean_object* v___x_373_; 
lean_dec_ref(v___x_335_);
lean_dec_ref(v_e_329_);
v___x_372_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducibleStep___boxed(lean_object* v_e_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Meta_Sym_unfoldReducibleStep(v_e_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
return v_res_380_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0(lean_object* v_env_381_, lean_object* v_e_382_){
_start:
{
if (lean_obj_tag(v_e_382_) == 4)
{
lean_object* v_declName_383_; uint8_t v___x_384_; 
v_declName_383_ = lean_ctor_get(v_e_382_, 0);
lean_inc(v_declName_383_);
lean_dec_ref_known(v_e_382_, 2);
v___x_384_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_381_, v_declName_383_);
return v___x_384_;
}
else
{
uint8_t v___x_385_; 
lean_dec_ref(v_e_382_);
lean_dec_ref(v_env_381_);
v___x_385_ = 0;
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0___boxed(lean_object* v_env_386_, lean_object* v_e_387_){
_start:
{
uint8_t v_res_388_; lean_object* v_r_389_; 
v_res_388_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0(v_env_386_, v_e_387_);
v_r_389_ = lean_box(v_res_388_);
return v_r_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(lean_object* v_e_390_, lean_object* v_a_391_){
_start:
{
lean_object* v___x_393_; lean_object* v_env_394_; lean_object* v___f_395_; lean_object* v___x_396_; 
v___x_393_ = lean_st_ref_get(v_a_391_);
v_env_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc_ref(v_env_394_);
lean_dec(v___x_393_);
v___f_395_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_395_, 0, v_env_394_);
v___x_396_ = lean_find_expr(v___f_395_, v_e_390_);
lean_dec_ref(v___f_395_);
if (lean_obj_tag(v___x_396_) == 0)
{
uint8_t v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_397_ = 0;
v___x_398_ = lean_box(v___x_397_);
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
return v___x_399_;
}
else
{
lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_408_; 
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_408_ == 0)
{
lean_object* v_unused_409_; 
v_unused_409_ = lean_ctor_get(v___x_396_, 0);
lean_dec(v_unused_409_);
v___x_401_ = v___x_396_;
v_isShared_402_ = v_isSharedCheck_408_;
goto v_resetjp_400_;
}
else
{
lean_dec(v___x_396_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_408_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
uint8_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_403_ = 1;
v___x_404_ = lean_box(v___x_403_);
if (v_isShared_402_ == 0)
{
lean_ctor_set_tag(v___x_401_, 0);
lean_ctor_set(v___x_401_, 0, v___x_404_);
v___x_406_ = v___x_401_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___boxed(lean_object* v_e_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_410_, v_a_411_);
lean_dec(v_a_411_);
lean_dec_ref(v_e_410_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget(lean_object* v_e_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_414_, v_a_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___boxed(lean_object* v_e_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget(v_e_419_, v_a_420_, v_a_421_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec_ref(v_e_419_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___lam__0(lean_object* v_e_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v_e_424_);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___lam__0___boxed(lean_object* v_e_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Meta_Sym_unfoldReducible___lam__0(v_e_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_object* v_00_u03b1_439_, lean_object* v_x_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_apply_1(v_x_440_, lean_box(0));
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0___boxed(lean_object* v_00_u03b1_448_, lean_object* v_x_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(v_00_u03b1_448_, v_x_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
return v_res_455_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(lean_object* v_a_456_, lean_object* v_x_457_){
_start:
{
if (lean_obj_tag(v_x_457_) == 0)
{
uint8_t v___x_458_; 
v___x_458_ = 0;
return v___x_458_;
}
else
{
lean_object* v_key_459_; lean_object* v_tail_460_; uint8_t v___x_461_; 
v_key_459_ = lean_ctor_get(v_x_457_, 0);
v_tail_460_ = lean_ctor_get(v_x_457_, 2);
v___x_461_ = l_Lean_ExprStructEq_beq(v_key_459_, v_a_456_);
if (v___x_461_ == 0)
{
v_x_457_ = v_tail_460_;
goto _start;
}
else
{
return v___x_461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object* v_a_463_, lean_object* v_x_464_){
_start:
{
uint8_t v_res_465_; lean_object* v_r_466_; 
v_res_465_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_463_, v_x_464_);
lean_dec(v_x_464_);
lean_dec_ref(v_a_463_);
v_r_466_ = lean_box(v_res_465_);
return v_r_466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object* v_x_467_, lean_object* v_x_468_){
_start:
{
if (lean_obj_tag(v_x_468_) == 0)
{
return v_x_467_;
}
else
{
lean_object* v_key_469_; lean_object* v_value_470_; lean_object* v_tail_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_494_; 
v_key_469_ = lean_ctor_get(v_x_468_, 0);
v_value_470_ = lean_ctor_get(v_x_468_, 1);
v_tail_471_ = lean_ctor_get(v_x_468_, 2);
v_isSharedCheck_494_ = !lean_is_exclusive(v_x_468_);
if (v_isSharedCheck_494_ == 0)
{
v___x_473_ = v_x_468_;
v_isShared_474_ = v_isSharedCheck_494_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_tail_471_);
lean_inc(v_value_470_);
lean_inc(v_key_469_);
lean_dec(v_x_468_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_494_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; uint64_t v___x_476_; uint64_t v___x_477_; uint64_t v___x_478_; uint64_t v_fold_479_; uint64_t v___x_480_; uint64_t v___x_481_; uint64_t v___x_482_; size_t v___x_483_; size_t v___x_484_; size_t v___x_485_; size_t v___x_486_; size_t v___x_487_; lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_475_ = lean_array_get_size(v_x_467_);
v___x_476_ = l_Lean_ExprStructEq_hash(v_key_469_);
v___x_477_ = 32ULL;
v___x_478_ = lean_uint64_shift_right(v___x_476_, v___x_477_);
v_fold_479_ = lean_uint64_xor(v___x_476_, v___x_478_);
v___x_480_ = 16ULL;
v___x_481_ = lean_uint64_shift_right(v_fold_479_, v___x_480_);
v___x_482_ = lean_uint64_xor(v_fold_479_, v___x_481_);
v___x_483_ = lean_uint64_to_usize(v___x_482_);
v___x_484_ = lean_usize_of_nat(v___x_475_);
v___x_485_ = ((size_t)1ULL);
v___x_486_ = lean_usize_sub(v___x_484_, v___x_485_);
v___x_487_ = lean_usize_land(v___x_483_, v___x_486_);
v___x_488_ = lean_array_uget_borrowed(v_x_467_, v___x_487_);
lean_inc(v___x_488_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 2, v___x_488_);
v___x_490_ = v___x_473_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_key_469_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_value_470_);
lean_ctor_set(v_reuseFailAlloc_493_, 2, v___x_488_);
v___x_490_ = v_reuseFailAlloc_493_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_491_; 
v___x_491_ = lean_array_uset(v_x_467_, v___x_487_, v___x_490_);
v_x_467_ = v___x_491_;
v_x_468_ = v_tail_471_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object* v_i_495_, lean_object* v_source_496_, lean_object* v_target_497_){
_start:
{
lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_498_ = lean_array_get_size(v_source_496_);
v___x_499_ = lean_nat_dec_lt(v_i_495_, v___x_498_);
if (v___x_499_ == 0)
{
lean_dec_ref(v_source_496_);
lean_dec(v_i_495_);
return v_target_497_;
}
else
{
lean_object* v_es_500_; lean_object* v___x_501_; lean_object* v_source_502_; lean_object* v_target_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_es_500_ = lean_array_fget(v_source_496_, v_i_495_);
v___x_501_ = lean_box(0);
v_source_502_ = lean_array_fset(v_source_496_, v_i_495_, v___x_501_);
v_target_503_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_497_, v_es_500_);
v___x_504_ = lean_unsigned_to_nat(1u);
v___x_505_ = lean_nat_add(v_i_495_, v___x_504_);
lean_dec(v_i_495_);
v_i_495_ = v___x_505_;
v_source_496_ = v_source_502_;
v_target_497_ = v_target_503_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(lean_object* v_data_507_){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v_nbuckets_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_508_ = lean_array_get_size(v_data_507_);
v___x_509_ = lean_unsigned_to_nat(2u);
v_nbuckets_510_ = lean_nat_mul(v___x_508_, v___x_509_);
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = lean_box(0);
v___x_513_ = lean_mk_array(v_nbuckets_510_, v___x_512_);
v___x_514_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_511_, v_data_507_, v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(lean_object* v_a_515_, lean_object* v_b_516_, lean_object* v_x_517_){
_start:
{
if (lean_obj_tag(v_x_517_) == 0)
{
lean_dec(v_b_516_);
lean_dec_ref(v_a_515_);
return v_x_517_;
}
else
{
lean_object* v_key_518_; lean_object* v_value_519_; lean_object* v_tail_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_532_; 
v_key_518_ = lean_ctor_get(v_x_517_, 0);
v_value_519_ = lean_ctor_get(v_x_517_, 1);
v_tail_520_ = lean_ctor_get(v_x_517_, 2);
v_isSharedCheck_532_ = !lean_is_exclusive(v_x_517_);
if (v_isSharedCheck_532_ == 0)
{
v___x_522_ = v_x_517_;
v_isShared_523_ = v_isSharedCheck_532_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_tail_520_);
lean_inc(v_value_519_);
lean_inc(v_key_518_);
lean_dec(v_x_517_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_532_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
uint8_t v___x_524_; 
v___x_524_ = l_Lean_ExprStructEq_beq(v_key_518_, v_a_515_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_525_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_515_, v_b_516_, v_tail_520_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 2, v___x_525_);
v___x_527_ = v___x_522_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_key_518_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_value_519_);
lean_ctor_set(v_reuseFailAlloc_528_, 2, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
else
{
lean_object* v___x_530_; 
lean_dec(v_value_519_);
lean_dec(v_key_518_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 1, v_b_516_);
lean_ctor_set(v___x_522_, 0, v_a_515_);
v___x_530_ = v___x_522_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_515_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_b_516_);
lean_ctor_set(v_reuseFailAlloc_531_, 2, v_tail_520_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(lean_object* v_m_533_, lean_object* v_a_534_, lean_object* v_b_535_){
_start:
{
lean_object* v_size_536_; lean_object* v_buckets_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_580_; 
v_size_536_ = lean_ctor_get(v_m_533_, 0);
v_buckets_537_ = lean_ctor_get(v_m_533_, 1);
v_isSharedCheck_580_ = !lean_is_exclusive(v_m_533_);
if (v_isSharedCheck_580_ == 0)
{
v___x_539_ = v_m_533_;
v_isShared_540_ = v_isSharedCheck_580_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_buckets_537_);
lean_inc(v_size_536_);
lean_dec(v_m_533_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_580_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; uint64_t v___x_542_; uint64_t v___x_543_; uint64_t v___x_544_; uint64_t v_fold_545_; uint64_t v___x_546_; uint64_t v___x_547_; uint64_t v___x_548_; size_t v___x_549_; size_t v___x_550_; size_t v___x_551_; size_t v___x_552_; size_t v___x_553_; lean_object* v_bkt_554_; uint8_t v___x_555_; 
v___x_541_ = lean_array_get_size(v_buckets_537_);
v___x_542_ = l_Lean_ExprStructEq_hash(v_a_534_);
v___x_543_ = 32ULL;
v___x_544_ = lean_uint64_shift_right(v___x_542_, v___x_543_);
v_fold_545_ = lean_uint64_xor(v___x_542_, v___x_544_);
v___x_546_ = 16ULL;
v___x_547_ = lean_uint64_shift_right(v_fold_545_, v___x_546_);
v___x_548_ = lean_uint64_xor(v_fold_545_, v___x_547_);
v___x_549_ = lean_uint64_to_usize(v___x_548_);
v___x_550_ = lean_usize_of_nat(v___x_541_);
v___x_551_ = ((size_t)1ULL);
v___x_552_ = lean_usize_sub(v___x_550_, v___x_551_);
v___x_553_ = lean_usize_land(v___x_549_, v___x_552_);
v_bkt_554_ = lean_array_uget_borrowed(v_buckets_537_, v___x_553_);
v___x_555_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_534_, v_bkt_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v_size_x27_557_; lean_object* v___x_558_; lean_object* v_buckets_x27_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_556_ = lean_unsigned_to_nat(1u);
v_size_x27_557_ = lean_nat_add(v_size_536_, v___x_556_);
lean_dec(v_size_536_);
lean_inc(v_bkt_554_);
v___x_558_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_558_, 0, v_a_534_);
lean_ctor_set(v___x_558_, 1, v_b_535_);
lean_ctor_set(v___x_558_, 2, v_bkt_554_);
v_buckets_x27_559_ = lean_array_uset(v_buckets_537_, v___x_553_, v___x_558_);
v___x_560_ = lean_unsigned_to_nat(4u);
v___x_561_ = lean_nat_mul(v_size_x27_557_, v___x_560_);
v___x_562_ = lean_unsigned_to_nat(3u);
v___x_563_ = lean_nat_div(v___x_561_, v___x_562_);
lean_dec(v___x_561_);
v___x_564_ = lean_array_get_size(v_buckets_x27_559_);
v___x_565_ = lean_nat_dec_le(v___x_563_, v___x_564_);
lean_dec(v___x_563_);
if (v___x_565_ == 0)
{
lean_object* v_val_566_; lean_object* v___x_568_; 
v_val_566_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_559_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v_val_566_);
lean_ctor_set(v___x_539_, 0, v_size_x27_557_);
v___x_568_ = v___x_539_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_size_x27_557_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_val_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
else
{
lean_object* v___x_571_; 
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v_buckets_x27_559_);
lean_ctor_set(v___x_539_, 0, v_size_x27_557_);
v___x_571_ = v___x_539_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_size_x27_557_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_buckets_x27_559_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
else
{
lean_object* v___x_573_; lean_object* v_buckets_x27_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
lean_inc(v_bkt_554_);
v___x_573_ = lean_box(0);
v_buckets_x27_574_ = lean_array_uset(v_buckets_537_, v___x_553_, v___x_573_);
v___x_575_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_534_, v_b_535_, v_bkt_554_);
v___x_576_ = lean_array_uset(v_buckets_x27_574_, v___x_553_, v___x_575_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v___x_576_);
v___x_578_ = v___x_539_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_size_536_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(lean_object* v_a_581_, lean_object* v_e_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_585_ = lean_st_ref_take(v_a_581_);
v___x_586_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v___x_585_, v_e_582_, v_a_583_);
v___x_587_ = lean_st_ref_set(v_a_581_, v___x_586_);
v___x_588_ = lean_box(0);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed(lean_object* v_a_589_, lean_object* v_e_590_, lean_object* v_a_591_, lean_object* v___y_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(v_a_589_, v_e_590_, v_a_591_);
lean_dec(v_a_589_);
return v_res_593_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = l_Lean_maxRecDepthErrorMessage;
v___x_600_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
return v___x_600_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
v___x_602_ = l_Lean_MessageData_ofFormat(v___x_601_);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_603_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
v___x_604_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2));
v___x_605_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v___x_603_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(lean_object* v_ref_606_){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_608_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_609_, 0, v_ref_606_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object* v_ref_611_, lean_object* v___y_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_611_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(lean_object* v_x_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v___y_622_; lean_object* v_fileName_631_; lean_object* v_fileMap_632_; lean_object* v_options_633_; lean_object* v_currRecDepth_634_; lean_object* v_maxRecDepth_635_; lean_object* v_ref_636_; lean_object* v_currNamespace_637_; lean_object* v_openDecls_638_; lean_object* v_initHeartbeats_639_; lean_object* v_maxHeartbeats_640_; lean_object* v_quotContext_641_; lean_object* v_currMacroScope_642_; uint8_t v_diag_643_; lean_object* v_cancelTk_x3f_644_; uint8_t v_suppressElabErrors_645_; lean_object* v_inheritedTraceOptions_646_; lean_object* v___x_652_; uint8_t v___x_653_; 
v_fileName_631_ = lean_ctor_get(v___y_618_, 0);
v_fileMap_632_ = lean_ctor_get(v___y_618_, 1);
v_options_633_ = lean_ctor_get(v___y_618_, 2);
v_currRecDepth_634_ = lean_ctor_get(v___y_618_, 3);
v_maxRecDepth_635_ = lean_ctor_get(v___y_618_, 4);
v_ref_636_ = lean_ctor_get(v___y_618_, 5);
v_currNamespace_637_ = lean_ctor_get(v___y_618_, 6);
v_openDecls_638_ = lean_ctor_get(v___y_618_, 7);
v_initHeartbeats_639_ = lean_ctor_get(v___y_618_, 8);
v_maxHeartbeats_640_ = lean_ctor_get(v___y_618_, 9);
v_quotContext_641_ = lean_ctor_get(v___y_618_, 10);
v_currMacroScope_642_ = lean_ctor_get(v___y_618_, 11);
v_diag_643_ = lean_ctor_get_uint8(v___y_618_, sizeof(void*)*14);
v_cancelTk_x3f_644_ = lean_ctor_get(v___y_618_, 12);
v_suppressElabErrors_645_ = lean_ctor_get_uint8(v___y_618_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_646_ = lean_ctor_get(v___y_618_, 13);
v___x_652_ = lean_unsigned_to_nat(0u);
v___x_653_ = lean_nat_dec_eq(v_maxRecDepth_635_, v___x_652_);
if (v___x_653_ == 0)
{
uint8_t v___x_654_; 
v___x_654_ = lean_nat_dec_eq(v_currRecDepth_634_, v_maxRecDepth_635_);
if (v___x_654_ == 0)
{
goto v___jp_647_;
}
else
{
lean_object* v___x_655_; 
lean_dec_ref(v_x_614_);
lean_inc(v_ref_636_);
v___x_655_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_636_);
v___y_622_ = v___x_655_;
goto v___jp_621_;
}
}
else
{
goto v___jp_647_;
}
v___jp_621_:
{
if (lean_obj_tag(v___y_622_) == 0)
{
return v___y_622_;
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
v_a_623_ = lean_ctor_get(v___y_622_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___y_622_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___y_622_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___y_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
v___jp_647_:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_648_ = lean_unsigned_to_nat(1u);
v___x_649_ = lean_nat_add(v_currRecDepth_634_, v___x_648_);
lean_inc_ref(v_inheritedTraceOptions_646_);
lean_inc(v_cancelTk_x3f_644_);
lean_inc(v_currMacroScope_642_);
lean_inc(v_quotContext_641_);
lean_inc(v_maxHeartbeats_640_);
lean_inc(v_initHeartbeats_639_);
lean_inc(v_openDecls_638_);
lean_inc(v_currNamespace_637_);
lean_inc(v_ref_636_);
lean_inc(v_maxRecDepth_635_);
lean_inc_ref(v_options_633_);
lean_inc_ref(v_fileMap_632_);
lean_inc_ref(v_fileName_631_);
v___x_650_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_650_, 0, v_fileName_631_);
lean_ctor_set(v___x_650_, 1, v_fileMap_632_);
lean_ctor_set(v___x_650_, 2, v_options_633_);
lean_ctor_set(v___x_650_, 3, v___x_649_);
lean_ctor_set(v___x_650_, 4, v_maxRecDepth_635_);
lean_ctor_set(v___x_650_, 5, v_ref_636_);
lean_ctor_set(v___x_650_, 6, v_currNamespace_637_);
lean_ctor_set(v___x_650_, 7, v_openDecls_638_);
lean_ctor_set(v___x_650_, 8, v_initHeartbeats_639_);
lean_ctor_set(v___x_650_, 9, v_maxHeartbeats_640_);
lean_ctor_set(v___x_650_, 10, v_quotContext_641_);
lean_ctor_set(v___x_650_, 11, v_currMacroScope_642_);
lean_ctor_set(v___x_650_, 12, v_cancelTk_x3f_644_);
lean_ctor_set(v___x_650_, 13, v_inheritedTraceOptions_646_);
lean_ctor_set_uint8(v___x_650_, sizeof(void*)*14, v_diag_643_);
lean_ctor_set_uint8(v___x_650_, sizeof(void*)*14 + 1, v_suppressElabErrors_645_);
lean_inc(v___y_619_);
lean_inc(v___y_617_);
lean_inc_ref(v___y_616_);
lean_inc(v___y_615_);
v___x_651_ = lean_apply_6(v_x_614_, v___y_615_, v___y_616_, v___y_617_, v___x_650_, v___y_619_, lean_box(0));
v___y_622_ = v___x_651_;
goto v___jp_621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg___boxed(lean_object* v_x_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_664_, lean_object* v_x_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_apply_1(v_x_665_, lean_box(0));
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_673_, lean_object* v_x_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(v_00_u03b1_673_, v_x_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_a_681_, lean_object* v_x_682_){
_start:
{
if (lean_obj_tag(v_x_682_) == 0)
{
lean_object* v___x_683_; 
v___x_683_ = lean_box(0);
return v___x_683_;
}
else
{
lean_object* v_key_684_; lean_object* v_value_685_; lean_object* v_tail_686_; uint8_t v___x_687_; 
v_key_684_ = lean_ctor_get(v_x_682_, 0);
v_value_685_ = lean_ctor_get(v_x_682_, 1);
v_tail_686_ = lean_ctor_get(v_x_682_, 2);
v___x_687_ = l_Lean_ExprStructEq_beq(v_key_684_, v_a_681_);
if (v___x_687_ == 0)
{
v_x_682_ = v_tail_686_;
goto _start;
}
else
{
lean_object* v___x_689_; 
lean_inc(v_value_685_);
v___x_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_689_, 0, v_value_685_);
return v___x_689_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_a_690_, lean_object* v_x_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_690_, v_x_691_);
lean_dec(v_x_691_);
lean_dec_ref(v_a_690_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(lean_object* v_m_693_, lean_object* v_a_694_){
_start:
{
lean_object* v_buckets_695_; lean_object* v___x_696_; uint64_t v___x_697_; uint64_t v___x_698_; uint64_t v___x_699_; uint64_t v_fold_700_; uint64_t v___x_701_; uint64_t v___x_702_; uint64_t v___x_703_; size_t v___x_704_; size_t v___x_705_; size_t v___x_706_; size_t v___x_707_; size_t v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v_buckets_695_ = lean_ctor_get(v_m_693_, 1);
v___x_696_ = lean_array_get_size(v_buckets_695_);
v___x_697_ = l_Lean_ExprStructEq_hash(v_a_694_);
v___x_698_ = 32ULL;
v___x_699_ = lean_uint64_shift_right(v___x_697_, v___x_698_);
v_fold_700_ = lean_uint64_xor(v___x_697_, v___x_699_);
v___x_701_ = 16ULL;
v___x_702_ = lean_uint64_shift_right(v_fold_700_, v___x_701_);
v___x_703_ = lean_uint64_xor(v_fold_700_, v___x_702_);
v___x_704_ = lean_uint64_to_usize(v___x_703_);
v___x_705_ = lean_usize_of_nat(v___x_696_);
v___x_706_ = ((size_t)1ULL);
v___x_707_ = lean_usize_sub(v___x_705_, v___x_706_);
v___x_708_ = lean_usize_land(v___x_704_, v___x_707_);
v___x_709_ = lean_array_uget_borrowed(v_buckets_695_, v___x_708_);
v___x_710_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_694_, v___x_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_m_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_m_711_, v_a_712_);
lean_dec_ref(v_a_712_);
lean_dec_ref(v_m_711_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(lean_object* v___x_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_714_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object* v___x_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(v___x_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object* v_k_728_, lean_object* v___y_729_, lean_object* v_b_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v___x_736_; 
lean_inc(v___y_734_);
lean_inc_ref(v___y_733_);
lean_inc(v___y_732_);
lean_inc_ref(v___y_731_);
lean_inc(v___y_729_);
v___x_736_ = lean_apply_7(v_k_728_, v_b_730_, v___y_729_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, lean_box(0));
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_737_, lean_object* v___y_738_, lean_object* v_b_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_737_, v___y_738_, v_b_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_738_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_name_746_, uint8_t v_bi_747_, lean_object* v_type_748_, lean_object* v_k_749_, uint8_t v_kind_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v___f_757_; lean_object* v___x_758_; 
lean_inc(v___y_751_);
v___f_757_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_757_, 0, v_k_749_);
lean_closure_set(v___f_757_, 1, v___y_751_);
v___x_758_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_746_, v_bi_747_, v_type_748_, v___f_757_, v_kind_750_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
if (lean_obj_tag(v___x_758_) == 0)
{
return v___x_758_;
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_name_767_, lean_object* v_bi_768_, lean_object* v_type_769_, lean_object* v_k_770_, lean_object* v_kind_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
uint8_t v_bi_boxed_778_; uint8_t v_kind_boxed_779_; lean_object* v_res_780_; 
v_bi_boxed_778_ = lean_unbox(v_bi_768_);
v_kind_boxed_779_ = lean_unbox(v_kind_771_);
v_res_780_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_767_, v_bi_boxed_778_, v_type_769_, v_k_770_, v_kind_boxed_779_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(lean_object* v_name_781_, lean_object* v_type_782_, lean_object* v_val_783_, lean_object* v_k_784_, uint8_t v_nondep_785_, uint8_t v_kind_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___f_793_; lean_object* v___x_794_; 
lean_inc(v___y_787_);
v___f_793_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_793_, 0, v_k_784_);
lean_closure_set(v___f_793_, 1, v___y_787_);
v___x_794_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_781_, v_type_782_, v_val_783_, v___f_793_, v_nondep_785_, v_kind_786_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
if (lean_obj_tag(v___x_794_) == 0)
{
return v___x_794_;
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_794_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_794_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object* v_name_803_, lean_object* v_type_804_, lean_object* v_val_805_, lean_object* v_k_806_, lean_object* v_nondep_807_, lean_object* v_kind_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
uint8_t v_nondep_boxed_815_; uint8_t v_kind_boxed_816_; lean_object* v_res_817_; 
v_nondep_boxed_815_ = lean_unbox(v_nondep_807_);
v_kind_boxed_816_ = lean_unbox(v_kind_808_);
v_res_817_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_803_, v_type_804_, v_val_805_, v_k_806_, v_nondep_boxed_815_, v_kind_boxed_816_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(lean_object* v_fvars_821_, lean_object* v_pre_822_, lean_object* v_post_823_, uint8_t v_usedLetOnly_824_, uint8_t v_skipConstInApp_825_, uint8_t v_skipInstances_826_, lean_object* v_body_827_, lean_object* v_x_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = lean_array_push(v_fvars_821_, v_x_828_);
v___x_836_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_822_, v_post_823_, v_usedLetOnly_824_, v_skipConstInApp_825_, v_skipInstances_826_, v___x_835_, v_body_827_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed(lean_object* v_fvars_837_, lean_object* v_pre_838_, lean_object* v_post_839_, lean_object* v_usedLetOnly_840_, lean_object* v_skipConstInApp_841_, lean_object* v_skipInstances_842_, lean_object* v_body_843_, lean_object* v_x_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
uint8_t v_usedLetOnly_boxed_851_; uint8_t v_skipConstInApp_boxed_852_; uint8_t v_skipInstances_boxed_853_; lean_object* v_res_854_; 
v_usedLetOnly_boxed_851_ = lean_unbox(v_usedLetOnly_840_);
v_skipConstInApp_boxed_852_ = lean_unbox(v_skipConstInApp_841_);
v_skipInstances_boxed_853_ = lean_unbox(v_skipInstances_842_);
v_res_854_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(v_fvars_837_, v_pre_838_, v_post_839_, v_usedLetOnly_boxed_851_, v_skipConstInApp_boxed_852_, v_skipInstances_boxed_853_, v_body_843_, v_x_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(lean_object* v_pre_855_, lean_object* v_post_856_, uint8_t v_usedLetOnly_857_, uint8_t v_skipConstInApp_858_, uint8_t v_skipInstances_859_, lean_object* v_e_860_, lean_object* v_a_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v___x_867_; 
lean_inc_ref(v_post_856_);
lean_inc(v___y_865_);
lean_inc_ref(v___y_864_);
lean_inc(v___y_863_);
lean_inc_ref(v___y_862_);
lean_inc_ref(v_e_860_);
v___x_867_ = lean_apply_6(v_post_856_, v_e_860_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, lean_box(0));
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_886_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_886_ == 0)
{
v___x_870_ = v___x_867_;
v_isShared_871_ = v_isSharedCheck_886_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_867_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_886_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
switch(lean_obj_tag(v_a_868_))
{
case 0:
{
lean_object* v_e_872_; lean_object* v___x_874_; 
lean_dec_ref(v_e_860_);
lean_dec_ref(v_post_856_);
lean_dec_ref(v_pre_855_);
v_e_872_ = lean_ctor_get(v_a_868_, 0);
lean_inc_ref(v_e_872_);
lean_dec_ref_known(v_a_868_, 1);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v_e_872_);
v___x_874_ = v___x_870_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_e_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
case 1:
{
lean_object* v_e_876_; lean_object* v___x_877_; 
lean_del_object(v___x_870_);
lean_dec_ref(v_e_860_);
v_e_876_ = lean_ctor_get(v_a_868_, 0);
lean_inc_ref(v_e_876_);
lean_dec_ref_known(v_a_868_, 1);
v___x_877_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_855_, v_post_856_, v_usedLetOnly_857_, v_skipConstInApp_858_, v_skipInstances_859_, v_e_876_, v_a_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
return v___x_877_;
}
default: 
{
lean_object* v_e_x3f_878_; 
lean_dec_ref(v_post_856_);
lean_dec_ref(v_pre_855_);
v_e_x3f_878_ = lean_ctor_get(v_a_868_, 0);
lean_inc(v_e_x3f_878_);
lean_dec_ref_known(v_a_868_, 1);
if (lean_obj_tag(v_e_x3f_878_) == 0)
{
lean_object* v___x_880_; 
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v_e_860_);
v___x_880_ = v___x_870_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_e_860_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
else
{
lean_object* v_val_882_; lean_object* v___x_884_; 
lean_dec_ref(v_e_860_);
v_val_882_ = lean_ctor_get(v_e_x3f_878_, 0);
lean_inc(v_val_882_);
lean_dec_ref_known(v_e_x3f_878_, 1);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v_val_882_);
v___x_884_ = v___x_870_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_val_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_dec_ref(v_e_860_);
lean_dec_ref(v_post_856_);
lean_dec_ref(v_pre_855_);
v_a_887_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_867_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_867_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(lean_object* v_pre_895_, lean_object* v_post_896_, uint8_t v_usedLetOnly_897_, uint8_t v_skipConstInApp_898_, uint8_t v_skipInstances_899_, lean_object* v_fvars_900_, lean_object* v_e_901_, lean_object* v_a_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
if (lean_obj_tag(v_e_901_) == 6)
{
lean_object* v_binderName_908_; lean_object* v_binderType_909_; lean_object* v_body_910_; uint8_t v_binderInfo_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v_binderName_908_ = lean_ctor_get(v_e_901_, 0);
lean_inc(v_binderName_908_);
v_binderType_909_ = lean_ctor_get(v_e_901_, 1);
lean_inc_ref(v_binderType_909_);
v_body_910_ = lean_ctor_get(v_e_901_, 2);
lean_inc_ref(v_body_910_);
v_binderInfo_911_ = lean_ctor_get_uint8(v_e_901_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_901_, 3);
v___x_912_ = lean_expr_instantiate_rev(v_binderType_909_, v_fvars_900_);
lean_dec_ref(v_binderType_909_);
lean_inc_ref(v_post_896_);
lean_inc_ref(v_pre_895_);
v___x_913_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_895_, v_post_896_, v_usedLetOnly_897_, v_skipConstInApp_898_, v_skipInstances_899_, v___x_912_, v_a_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___f_918_; uint8_t v___x_919_; lean_object* v___x_920_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref_known(v___x_913_, 1);
v___x_915_ = lean_box(v_usedLetOnly_897_);
v___x_916_ = lean_box(v_skipConstInApp_898_);
v___x_917_ = lean_box(v_skipInstances_899_);
v___f_918_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_918_, 0, v_fvars_900_);
lean_closure_set(v___f_918_, 1, v_pre_895_);
lean_closure_set(v___f_918_, 2, v_post_896_);
lean_closure_set(v___f_918_, 3, v___x_915_);
lean_closure_set(v___f_918_, 4, v___x_916_);
lean_closure_set(v___f_918_, 5, v___x_917_);
lean_closure_set(v___f_918_, 6, v_body_910_);
v___x_919_ = 0;
v___x_920_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_908_, v_binderInfo_911_, v_a_914_, v___f_918_, v___x_919_, v_a_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
return v___x_920_;
}
else
{
lean_dec_ref(v_body_910_);
lean_dec(v_binderName_908_);
lean_dec_ref(v_fvars_900_);
lean_dec_ref(v_post_896_);
lean_dec_ref(v_pre_895_);
return v___x_913_;
}
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = lean_expr_instantiate_rev(v_e_901_, v_fvars_900_);
lean_dec_ref(v_e_901_);
lean_inc_ref(v_post_896_);
lean_inc_ref(v_pre_895_);
v___x_922_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_895_, v_post_896_, v_usedLetOnly_897_, v_skipConstInApp_898_, v_skipInstances_899_, v___x_921_, v_a_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; uint8_t v___x_924_; uint8_t v___x_925_; uint8_t v___x_926_; lean_object* v___x_927_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_a_923_);
lean_dec_ref_known(v___x_922_, 1);
v___x_924_ = 0;
v___x_925_ = 1;
v___x_926_ = 1;
v___x_927_ = l_Lean_Meta_mkLambdaFVars(v_fvars_900_, v_a_923_, v___x_924_, v_usedLetOnly_897_, v___x_924_, v___x_925_, v___x_926_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec_ref(v_fvars_900_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; lean_object* v___x_929_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
lean_dec_ref_known(v___x_927_, 1);
v___x_929_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_895_, v_post_896_, v_usedLetOnly_897_, v_skipConstInApp_898_, v_skipInstances_899_, v_a_928_, v_a_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
return v___x_929_;
}
else
{
lean_dec_ref(v_post_896_);
lean_dec_ref(v_pre_895_);
return v___x_927_;
}
}
else
{
lean_dec_ref(v_fvars_900_);
lean_dec_ref(v_post_896_);
lean_dec_ref(v_pre_895_);
return v___x_922_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(lean_object* v_fvars_930_, lean_object* v_pre_931_, lean_object* v_post_932_, uint8_t v_usedLetOnly_933_, uint8_t v_skipConstInApp_934_, uint8_t v_skipInstances_935_, lean_object* v_body_936_, lean_object* v_x_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = lean_array_push(v_fvars_930_, v_x_937_);
v___x_945_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_931_, v_post_932_, v_usedLetOnly_933_, v_skipConstInApp_934_, v_skipInstances_935_, v___x_944_, v_body_936_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed(lean_object* v_fvars_946_, lean_object* v_pre_947_, lean_object* v_post_948_, lean_object* v_usedLetOnly_949_, lean_object* v_skipConstInApp_950_, lean_object* v_skipInstances_951_, lean_object* v_body_952_, lean_object* v_x_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
uint8_t v_usedLetOnly_boxed_960_; uint8_t v_skipConstInApp_boxed_961_; uint8_t v_skipInstances_boxed_962_; lean_object* v_res_963_; 
v_usedLetOnly_boxed_960_ = lean_unbox(v_usedLetOnly_949_);
v_skipConstInApp_boxed_961_ = lean_unbox(v_skipConstInApp_950_);
v_skipInstances_boxed_962_ = lean_unbox(v_skipInstances_951_);
v_res_963_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(v_fvars_946_, v_pre_947_, v_post_948_, v_usedLetOnly_boxed_960_, v_skipConstInApp_boxed_961_, v_skipInstances_boxed_962_, v_body_952_, v_x_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(lean_object* v_pre_964_, lean_object* v_post_965_, uint8_t v_usedLetOnly_966_, uint8_t v_skipConstInApp_967_, uint8_t v_skipInstances_968_, lean_object* v_fvars_969_, lean_object* v_e_970_, lean_object* v_a_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
if (lean_obj_tag(v_e_970_) == 8)
{
lean_object* v_declName_977_; lean_object* v_type_978_; lean_object* v_value_979_; lean_object* v_body_980_; uint8_t v_nondep_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_declName_977_ = lean_ctor_get(v_e_970_, 0);
lean_inc(v_declName_977_);
v_type_978_ = lean_ctor_get(v_e_970_, 1);
lean_inc_ref(v_type_978_);
v_value_979_ = lean_ctor_get(v_e_970_, 2);
lean_inc_ref(v_value_979_);
v_body_980_ = lean_ctor_get(v_e_970_, 3);
lean_inc_ref(v_body_980_);
v_nondep_981_ = lean_ctor_get_uint8(v_e_970_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_970_, 4);
v___x_982_ = lean_expr_instantiate_rev(v_type_978_, v_fvars_969_);
lean_dec_ref(v_type_978_);
lean_inc_ref(v_post_965_);
lean_inc_ref(v_pre_964_);
v___x_983_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_964_, v_post_965_, v_usedLetOnly_966_, v_skipConstInApp_967_, v_skipInstances_968_, v___x_982_, v_a_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref_known(v___x_983_, 1);
v___x_985_ = lean_expr_instantiate_rev(v_value_979_, v_fvars_969_);
lean_dec_ref(v_value_979_);
lean_inc_ref(v_post_965_);
lean_inc_ref(v_pre_964_);
v___x_986_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_964_, v_post_965_, v_usedLetOnly_966_, v_skipConstInApp_967_, v_skipInstances_968_, v___x_985_, v_a_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___f_991_; uint8_t v___x_992_; lean_object* v___x_993_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_986_, 1);
v___x_988_ = lean_box(v_usedLetOnly_966_);
v___x_989_ = lean_box(v_skipConstInApp_967_);
v___x_990_ = lean_box(v_skipInstances_968_);
v___f_991_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_991_, 0, v_fvars_969_);
lean_closure_set(v___f_991_, 1, v_pre_964_);
lean_closure_set(v___f_991_, 2, v_post_965_);
lean_closure_set(v___f_991_, 3, v___x_988_);
lean_closure_set(v___f_991_, 4, v___x_989_);
lean_closure_set(v___f_991_, 5, v___x_990_);
lean_closure_set(v___f_991_, 6, v_body_980_);
v___x_992_ = 0;
v___x_993_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_977_, v_a_984_, v_a_987_, v___f_991_, v_nondep_981_, v___x_992_, v_a_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
return v___x_993_;
}
else
{
lean_dec(v_a_984_);
lean_dec_ref(v_body_980_);
lean_dec(v_declName_977_);
lean_dec_ref(v_fvars_969_);
lean_dec_ref(v_post_965_);
lean_dec_ref(v_pre_964_);
return v___x_986_;
}
}
else
{
lean_dec_ref(v_body_980_);
lean_dec_ref(v_value_979_);
lean_dec(v_declName_977_);
lean_dec_ref(v_fvars_969_);
lean_dec_ref(v_post_965_);
lean_dec_ref(v_pre_964_);
return v___x_983_;
}
}
else
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_expr_instantiate_rev(v_e_970_, v_fvars_969_);
lean_dec_ref(v_e_970_);
lean_inc_ref(v_post_965_);
lean_inc_ref(v_pre_964_);
v___x_995_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_964_, v_post_965_, v_usedLetOnly_966_, v_skipConstInApp_967_, v_skipInstances_968_, v___x_994_, v_a_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; uint8_t v___x_997_; uint8_t v___x_998_; lean_object* v___x_999_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_996_);
lean_dec_ref_known(v___x_995_, 1);
v___x_997_ = 0;
v___x_998_ = 1;
v___x_999_ = l_Lean_Meta_mkLetFVars(v_fvars_969_, v_a_996_, v_usedLetOnly_966_, v___x_997_, v___x_998_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec_ref(v_fvars_969_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_999_, 1);
v___x_1001_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_964_, v_post_965_, v_usedLetOnly_966_, v_skipConstInApp_967_, v_skipInstances_968_, v_a_1000_, v_a_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
return v___x_1001_;
}
else
{
lean_dec_ref(v_post_965_);
lean_dec_ref(v_pre_964_);
return v___x_999_;
}
}
else
{
lean_dec_ref(v_fvars_969_);
lean_dec_ref(v_post_965_);
lean_dec_ref(v_pre_964_);
return v___x_995_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1002_; lean_object* v_dummy_1003_; 
v___x_1002_ = lean_box(0);
v_dummy_1003_ = l_Lean_Expr_sort___override(v___x_1002_);
return v_dummy_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(lean_object* v_pre_1004_, lean_object* v_post_1005_, uint8_t v_usedLetOnly_1006_, uint8_t v_skipConstInApp_1007_, uint8_t v_skipInstances_1008_, size_t v_sz_1009_, size_t v_i_1010_, lean_object* v_bs_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
uint8_t v___x_1018_; 
v___x_1018_ = lean_usize_dec_lt(v_i_1010_, v_sz_1009_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; 
lean_dec_ref(v_post_1005_);
lean_dec_ref(v_pre_1004_);
v___x_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1019_, 0, v_bs_1011_);
return v___x_1019_;
}
else
{
lean_object* v_v_1020_; lean_object* v___x_1021_; 
v_v_1020_ = lean_array_uget_borrowed(v_bs_1011_, v_i_1010_);
lean_inc(v_v_1020_);
lean_inc_ref(v_post_1005_);
lean_inc_ref(v_pre_1004_);
v___x_1021_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1004_, v_post_1005_, v_usedLetOnly_1006_, v_skipConstInApp_1007_, v_skipInstances_1008_, v_v_1020_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1023_; lean_object* v_bs_x27_1024_; size_t v___x_1025_; size_t v___x_1026_; lean_object* v___x_1027_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1021_, 1);
v___x_1023_ = lean_unsigned_to_nat(0u);
v_bs_x27_1024_ = lean_array_uset(v_bs_1011_, v_i_1010_, v___x_1023_);
v___x_1025_ = ((size_t)1ULL);
v___x_1026_ = lean_usize_add(v_i_1010_, v___x_1025_);
v___x_1027_ = lean_array_uset(v_bs_x27_1024_, v_i_1010_, v_a_1022_);
v_i_1010_ = v___x_1026_;
v_bs_1011_ = v___x_1027_;
goto _start;
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
lean_dec_ref(v_bs_1011_);
lean_dec_ref(v_post_1005_);
lean_dec_ref(v_pre_1004_);
v_a_1029_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1021_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1021_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_pre_1037_, lean_object* v_post_1038_, uint8_t v_usedLetOnly_1039_, uint8_t v_skipConstInApp_1040_, uint8_t v_skipInstances_1041_, lean_object* v___x_1042_, lean_object* v___y_1043_, lean_object* v_b_1044_, lean_object* v_a_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1037_, v_post_1038_, v_usedLetOnly_1039_, v_skipConstInApp_1040_, v_skipInstances_1041_, v___x_1042_, v___y_1043_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1061_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1061_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1061_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1056_ = lean_array_fset(v_b_1044_, v_a_1045_, v_a_1052_);
v___x_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1057_);
v___x_1059_ = v___x_1054_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec_ref(v_b_1044_);
v_a_1062_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1051_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1051_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_pre_1070_, lean_object* v_post_1071_, lean_object* v_usedLetOnly_1072_, lean_object* v_skipConstInApp_1073_, lean_object* v_skipInstances_1074_, lean_object* v___x_1075_, lean_object* v___y_1076_, lean_object* v_b_1077_, lean_object* v_a_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
uint8_t v_usedLetOnly_boxed_1084_; uint8_t v_skipConstInApp_boxed_1085_; uint8_t v_skipInstances_boxed_1086_; lean_object* v_res_1087_; 
v_usedLetOnly_boxed_1084_ = lean_unbox(v_usedLetOnly_1072_);
v_skipConstInApp_boxed_1085_ = lean_unbox(v_skipConstInApp_1073_);
v_skipInstances_boxed_1086_ = lean_unbox(v_skipInstances_1074_);
v_res_1087_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_1070_, v_post_1071_, v_usedLetOnly_boxed_1084_, v_skipConstInApp_boxed_1085_, v_skipInstances_boxed_1086_, v___x_1075_, v___y_1076_, v_b_1077_, v_a_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v_a_1078_);
lean_dec(v___y_1076_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(lean_object* v_upperBound_1088_, lean_object* v___x_1089_, lean_object* v_pre_1090_, lean_object* v_post_1091_, uint8_t v_usedLetOnly_1092_, uint8_t v_skipConstInApp_1093_, uint8_t v_skipInstances_1094_, lean_object* v_a_1095_, lean_object* v_b_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v___y_1104_; uint8_t v___x_1127_; 
v___x_1127_ = lean_nat_dec_lt(v_a_1095_, v_upperBound_1088_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; 
lean_dec(v_a_1095_);
lean_dec_ref(v_post_1091_);
lean_dec_ref(v_pre_1090_);
v___x_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1128_, 0, v_b_1096_);
return v___x_1128_;
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1129_ = lean_array_fget_borrowed(v_b_1096_, v_a_1095_);
v___x_1130_ = lean_array_get_size(v___x_1089_);
v___x_1131_ = lean_nat_dec_lt(v_a_1095_, v___x_1130_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___f_1135_; 
lean_inc(v___x_1129_);
v___x_1132_ = lean_box(v_usedLetOnly_1092_);
v___x_1133_ = lean_box(v_skipConstInApp_1093_);
v___x_1134_ = lean_box(v_skipInstances_1094_);
lean_inc(v_a_1095_);
lean_inc(v___y_1097_);
lean_inc_ref(v_post_1091_);
lean_inc_ref(v_pre_1090_);
v___f_1135_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1135_, 0, v_pre_1090_);
lean_closure_set(v___f_1135_, 1, v_post_1091_);
lean_closure_set(v___f_1135_, 2, v___x_1132_);
lean_closure_set(v___f_1135_, 3, v___x_1133_);
lean_closure_set(v___f_1135_, 4, v___x_1134_);
lean_closure_set(v___f_1135_, 5, v___x_1129_);
lean_closure_set(v___f_1135_, 6, v___y_1097_);
lean_closure_set(v___f_1135_, 7, v_b_1096_);
lean_closure_set(v___f_1135_, 8, v_a_1095_);
v___y_1104_ = v___f_1135_;
goto v___jp_1103_;
}
else
{
lean_object* v___x_1136_; uint8_t v_isInstance_1137_; 
v___x_1136_ = lean_array_fget_borrowed(v___x_1089_, v_a_1095_);
v_isInstance_1137_ = lean_ctor_get_uint8(v___x_1136_, sizeof(void*)*1 + 4);
if (v_isInstance_1137_ == 0)
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___f_1141_; 
lean_inc(v___x_1129_);
v___x_1138_ = lean_box(v_usedLetOnly_1092_);
v___x_1139_ = lean_box(v_skipConstInApp_1093_);
v___x_1140_ = lean_box(v_skipInstances_1094_);
lean_inc(v_a_1095_);
lean_inc(v___y_1097_);
lean_inc_ref(v_post_1091_);
lean_inc_ref(v_pre_1090_);
v___f_1141_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1141_, 0, v_pre_1090_);
lean_closure_set(v___f_1141_, 1, v_post_1091_);
lean_closure_set(v___f_1141_, 2, v___x_1138_);
lean_closure_set(v___f_1141_, 3, v___x_1139_);
lean_closure_set(v___f_1141_, 4, v___x_1140_);
lean_closure_set(v___f_1141_, 5, v___x_1129_);
lean_closure_set(v___f_1141_, 6, v___y_1097_);
lean_closure_set(v___f_1141_, 7, v_b_1096_);
lean_closure_set(v___f_1141_, 8, v_a_1095_);
v___y_1104_ = v___f_1141_;
goto v___jp_1103_;
}
else
{
lean_object* v___x_1142_; lean_object* v___f_1143_; 
v___x_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1142_, 0, v_b_1096_);
v___f_1143_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1143_, 0, v___x_1142_);
v___y_1104_ = v___f_1143_;
goto v___jp_1103_;
}
}
}
v___jp_1103_:
{
lean_object* v___x_1105_; 
lean_inc(v___y_1101_);
lean_inc_ref(v___y_1100_);
lean_inc(v___y_1099_);
lean_inc_ref(v___y_1098_);
v___x_1105_ = lean_apply_5(v___y_1104_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, lean_box(0));
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1118_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1108_ = v___x_1105_;
v_isShared_1109_ = v_isSharedCheck_1118_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1105_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1118_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
if (lean_obj_tag(v_a_1106_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1112_; 
lean_dec(v_a_1095_);
lean_dec_ref(v_post_1091_);
lean_dec_ref(v_pre_1090_);
v_a_1110_ = lean_ctor_get(v_a_1106_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v_a_1106_, 1);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v_a_1110_);
v___x_1112_ = v___x_1108_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1110_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_del_object(v___x_1108_);
v_a_1114_ = lean_ctor_get(v_a_1106_, 0);
lean_inc(v_a_1114_);
lean_dec_ref_known(v_a_1106_, 1);
v___x_1115_ = lean_unsigned_to_nat(1u);
v___x_1116_ = lean_nat_add(v_a_1095_, v___x_1115_);
lean_dec(v_a_1095_);
v_a_1095_ = v___x_1116_;
v_b_1096_ = v_a_1114_;
goto _start;
}
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec(v_a_1095_);
lean_dec_ref(v_post_1091_);
lean_dec_ref(v_pre_1090_);
v_a_1119_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1105_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1105_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(uint8_t v_skipInstances_1144_, lean_object* v_pre_1145_, lean_object* v_post_1146_, uint8_t v_usedLetOnly_1147_, uint8_t v_skipConstInApp_1148_, lean_object* v_x_1149_, lean_object* v_x_1150_, lean_object* v_x_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v_f_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; 
if (lean_obj_tag(v_x_1149_) == 5)
{
lean_object* v_fn_1207_; lean_object* v_arg_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v_fn_1207_ = lean_ctor_get(v_x_1149_, 0);
lean_inc_ref(v_fn_1207_);
v_arg_1208_ = lean_ctor_get(v_x_1149_, 1);
lean_inc_ref(v_arg_1208_);
lean_dec_ref_known(v_x_1149_, 2);
v___x_1209_ = lean_array_set(v_x_1150_, v_x_1151_, v_arg_1208_);
v___x_1210_ = lean_unsigned_to_nat(1u);
v___x_1211_ = lean_nat_sub(v_x_1151_, v___x_1210_);
lean_dec(v_x_1151_);
v_x_1149_ = v_fn_1207_;
v_x_1150_ = v___x_1209_;
v_x_1151_ = v___x_1211_;
goto _start;
}
else
{
lean_dec(v_x_1151_);
if (v_skipConstInApp_1148_ == 0)
{
goto v___jp_1204_;
}
else
{
uint8_t v___x_1213_; 
v___x_1213_ = l_Lean_Expr_isConst(v_x_1149_);
if (v___x_1213_ == 0)
{
goto v___jp_1204_;
}
else
{
v_f_1159_ = v_x_1149_;
v___y_1160_ = v___y_1152_;
v___y_1161_ = v___y_1153_;
v___y_1162_ = v___y_1154_;
v___y_1163_ = v___y_1155_;
v___y_1164_ = v___y_1156_;
goto v___jp_1158_;
}
}
}
v___jp_1158_:
{
if (v_skipInstances_1144_ == 0)
{
size_t v_sz_1165_; size_t v___x_1166_; lean_object* v___x_1167_; 
v_sz_1165_ = lean_array_size(v_x_1150_);
v___x_1166_ = ((size_t)0ULL);
lean_inc_ref(v_post_1146_);
lean_inc_ref(v_pre_1145_);
v___x_1167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_pre_1145_, v_post_1146_, v_usedLetOnly_1147_, v_skipConstInApp_1148_, v_skipInstances_1144_, v_sz_1165_, v___x_1166_, v_x_1150_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_a_1168_);
lean_dec_ref_known(v___x_1167_, 1);
v___x_1169_ = l_Lean_mkAppN(v_f_1159_, v_a_1168_);
lean_dec(v_a_1168_);
v___x_1170_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1145_, v_post_1146_, v_usedLetOnly_1147_, v_skipConstInApp_1148_, v_skipInstances_1144_, v___x_1169_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
return v___x_1170_;
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_dec_ref(v_f_1159_);
lean_dec_ref(v_post_1146_);
lean_dec_ref(v_pre_1145_);
v_a_1171_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1167_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1167_);
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
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = lean_array_get_size(v_x_1150_);
lean_inc_ref(v_f_1159_);
v___x_1180_ = l_Lean_Meta_getFunInfoNArgs(v_f_1159_, v___x_1179_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v_paramInfo_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1181_);
lean_dec_ref_known(v___x_1180_, 1);
v_paramInfo_1182_ = lean_ctor_get(v_a_1181_, 0);
lean_inc_ref(v_paramInfo_1182_);
lean_dec(v_a_1181_);
v___x_1183_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1146_);
lean_inc_ref(v_pre_1145_);
v___x_1184_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v___x_1179_, v_paramInfo_1182_, v_pre_1145_, v_post_1146_, v_usedLetOnly_1147_, v_skipConstInApp_1148_, v_skipInstances_1144_, v___x_1183_, v_x_1150_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec_ref(v_paramInfo_1182_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_a_1185_);
lean_dec_ref_known(v___x_1184_, 1);
v___x_1186_ = l_Lean_mkAppN(v_f_1159_, v_a_1185_);
lean_dec(v_a_1185_);
v___x_1187_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1145_, v_post_1146_, v_usedLetOnly_1147_, v_skipConstInApp_1148_, v_skipInstances_1144_, v___x_1186_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
return v___x_1187_;
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_dec_ref(v_f_1159_);
lean_dec_ref(v_post_1146_);
lean_dec_ref(v_pre_1145_);
v_a_1188_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1184_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1184_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec_ref(v_f_1159_);
lean_dec_ref(v_x_1150_);
lean_dec_ref(v_post_1146_);
lean_dec_ref(v_pre_1145_);
v_a_1196_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1180_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1180_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
v___jp_1204_:
{
lean_object* v___x_1205_; 
lean_inc_ref(v_post_1146_);
lean_inc_ref(v_pre_1145_);
v___x_1205_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1145_, v_post_1146_, v_usedLetOnly_1147_, v_skipConstInApp_1148_, v_skipInstances_1144_, v_x_1149_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1206_);
lean_dec_ref_known(v___x_1205_, 1);
v_f_1159_ = v_a_1206_;
v___y_1160_ = v___y_1152_;
v___y_1161_ = v___y_1153_;
v___y_1162_ = v___y_1154_;
v___y_1163_ = v___y_1155_;
v___y_1164_ = v___y_1156_;
goto v___jp_1158_;
}
else
{
lean_dec_ref(v_x_1150_);
lean_dec_ref(v_post_1146_);
lean_dec_ref(v_pre_1145_);
return v___x_1205_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(lean_object* v___x_1214_, lean_object* v_pre_1215_, lean_object* v_e_1216_, lean_object* v_post_1217_, uint8_t v_usedLetOnly_1218_, uint8_t v_skipConstInApp_1219_, uint8_t v_skipInstances_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_Core_checkSystem(v___x_1214_, v___y_1224_, v___y_1225_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v___x_1228_; 
lean_dec_ref_known(v___x_1227_, 1);
lean_inc_ref(v_pre_1215_);
lean_inc(v___y_1225_);
lean_inc_ref(v___y_1224_);
lean_inc(v___y_1223_);
lean_inc_ref(v___y_1222_);
lean_inc_ref(v_e_1216_);
v___x_1228_ = lean_apply_6(v_pre_1215_, v_e_1216_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, lean_box(0));
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1277_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1231_ = v___x_1228_;
v_isShared_1232_ = v_isSharedCheck_1277_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1228_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1277_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___y_1234_; 
switch(lean_obj_tag(v_a_1229_))
{
case 0:
{
lean_object* v_e_1269_; lean_object* v___x_1271_; 
lean_dec_ref(v_post_1217_);
lean_dec_ref(v_e_1216_);
lean_dec_ref(v_pre_1215_);
v_e_1269_ = lean_ctor_get(v_a_1229_, 0);
lean_inc_ref(v_e_1269_);
lean_dec_ref_known(v_a_1229_, 1);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v_e_1269_);
v___x_1271_ = v___x_1231_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_e_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
case 1:
{
lean_object* v_e_1273_; lean_object* v___x_1274_; 
lean_del_object(v___x_1231_);
lean_dec_ref(v_e_1216_);
v_e_1273_ = lean_ctor_get(v_a_1229_, 0);
lean_inc_ref(v_e_1273_);
lean_dec_ref_known(v_a_1229_, 1);
v___x_1274_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1215_, v_post_1217_, v_usedLetOnly_1218_, v_skipConstInApp_1219_, v_skipInstances_1220_, v_e_1273_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
return v___x_1274_;
}
default: 
{
lean_object* v_e_x3f_1275_; 
lean_del_object(v___x_1231_);
v_e_x3f_1275_ = lean_ctor_get(v_a_1229_, 0);
lean_inc(v_e_x3f_1275_);
lean_dec_ref_known(v_a_1229_, 1);
if (lean_obj_tag(v_e_x3f_1275_) == 0)
{
v___y_1234_ = v_e_1216_;
goto v___jp_1233_;
}
else
{
lean_object* v_val_1276_; 
lean_dec_ref(v_e_1216_);
v_val_1276_ = lean_ctor_get(v_e_x3f_1275_, 0);
lean_inc(v_val_1276_);
lean_dec_ref_known(v_e_x3f_1275_, 1);
v___y_1234_ = v_val_1276_;
goto v___jp_1233_;
}
}
}
v___jp_1233_:
{
switch(lean_obj_tag(v___y_1234_))
{
case 7:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1236_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1215_, v_post_1217_, v_usedLetOnly_1218_, v_skipConstInApp_1219_, v_skipInstances_1220_, v___x_1235_, v___y_1234_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
return v___x_1236_;
}
case 6:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1238_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_1215_, v_post_1217_, v_usedLetOnly_1218_, v_skipConstInApp_1219_, v_skipInstances_1220_, v___x_1237_, v___y_1234_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
return v___x_1238_;
}
case 8:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1240_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_1215_, v_post_1217_, v_usedLetOnly_1218_, v_skipConstInApp_1219_, v_skipInstances_1220_, v___x_1239_, v___y_1234_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
return v___x_1240_;
}
case 5:
{
lean_object* v_dummy_1241_; lean_object* v_nargs_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v_dummy_1241_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1);
v_nargs_1242_ = l_Lean_Expr_getAppNumArgs(v___y_1234_);
lean_inc(v_nargs_1242_);
v___x_1243_ = lean_mk_array(v_nargs_1242_, v_dummy_1241_);
v___x_1244_ = lean_unsigned_to_nat(1u);
v___x_1245_ = lean_nat_sub(v_nargs_1242_, v___x_1244_);
lean_dec(v_nargs_1242_);
v___x_1246_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_1220_, v_pre_1215_, v_post_1217_, v_usedLetOnly_1218_, v_skipConstInApp_1219_, v___y_1234_, v___x_1243_, v___x_1245_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
return v___x_1246_;
}
case 10:
{
lean_object* v_data_1247_; lean_object* v_expr_1248_; lean_object* v___x_1249_; 
v_data_1247_ = lean_ctor_get(v___y_1234_, 0);
v_expr_1248_ = lean_ctor_get(v___y_1234_, 1);
lean_inc_ref(v_expr_1248_);
lean_inc_ref(v_post_1217_);
lean_inc_ref(v_pre_1215_);
v___x_1249_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1215_, v_post_1217_, v_usedLetOnly_1218_, v_skipConstInApp_1219_, v_skipInstances_1220_, v_expr_1248_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; size_t v___x_1251_; size_t v___x_1252_; uint8_t v___x_1253_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1250_);
lean_dec_ref_known(v___x_1249_, 1);
v___x_1251_ = lean_ptr_addr(v_expr_1248_);
v___x_1252_ = lean_ptr_addr(v_a_1250_);
v___x_1253_ = lean_usize_dec_eq(v___x_1251_, v___x_1252_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
lean_inc(v_data_1247_);
lean_dec_ref_known(v___y_1234_, 2);
v___x_1254_ = l_Lean_Expr_mdata___override(v_data_1247_, v_a_1250_);
v___x_1255_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1215_, v_post_1217_, v_usedLetOnly_1218_, v_skipConstInApp_1219_, v_skipInstances_1220_, v___x_1254_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
return v___x_1255_;
}
else
{
lean_object* v___x_1256_; 
lean_dec(v_a_1250_);
v___x_1256_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1215_, v_post_1217_, v_usedLetOnly_1218_, v_skipConstInApp_1219_, v_skipInstances_1220_, v___y_1234_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
return v___x_1256_;
}
}
else
{
lean_dec_ref_known(v___y_1234_, 2);
lean_dec_ref(v_post_1217_);
lean_dec_ref(v_pre_1215_);
return v___x_1249_;
}
}
case 11:
{
lean_object* v_typeName_1257_; lean_object* v_idx_1258_; lean_object* v_struct_1259_; lean_object* v___x_1260_; 
v_typeName_1257_ = lean_ctor_get(v___y_1234_, 0);
v_idx_1258_ = lean_ctor_get(v___y_1234_, 1);
v_struct_1259_ = lean_ctor_get(v___y_1234_, 2);
lean_inc_ref(v_struct_1259_);
lean_inc_ref(v_post_1217_);
lean_inc_ref(v_pre_1215_);
v___x_1260_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1215_, v_post_1217_, v_usedLetOnly_1218_, v_skipConstInApp_1219_, v_skipInstances_1220_, v_struct_1259_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; size_t v___x_1262_; size_t v___x_1263_; uint8_t v___x_1264_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___x_1260_, 1);
v___x_1262_ = lean_ptr_addr(v_struct_1259_);
v___x_1263_ = lean_ptr_addr(v_a_1261_);
v___x_1264_ = lean_usize_dec_eq(v___x_1262_, v___x_1263_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_inc(v_idx_1258_);
lean_inc(v_typeName_1257_);
lean_dec_ref_known(v___y_1234_, 3);
v___x_1265_ = l_Lean_Expr_proj___override(v_typeName_1257_, v_idx_1258_, v_a_1261_);
v___x_1266_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1215_, v_post_1217_, v_usedLetOnly_1218_, v_skipConstInApp_1219_, v_skipInstances_1220_, v___x_1265_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
return v___x_1266_;
}
else
{
lean_object* v___x_1267_; 
lean_dec(v_a_1261_);
v___x_1267_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1215_, v_post_1217_, v_usedLetOnly_1218_, v_skipConstInApp_1219_, v_skipInstances_1220_, v___y_1234_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
return v___x_1267_;
}
}
else
{
lean_dec_ref_known(v___y_1234_, 3);
lean_dec_ref(v_post_1217_);
lean_dec_ref(v_pre_1215_);
return v___x_1260_;
}
}
default: 
{
lean_object* v___x_1268_; 
v___x_1268_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1215_, v_post_1217_, v_usedLetOnly_1218_, v_skipConstInApp_1219_, v_skipInstances_1220_, v___y_1234_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
return v___x_1268_;
}
}
}
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_dec_ref(v_post_1217_);
lean_dec_ref(v_e_1216_);
lean_dec_ref(v_pre_1215_);
v_a_1278_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1228_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1228_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec_ref(v_post_1217_);
lean_dec_ref(v_e_1216_);
lean_dec_ref(v_pre_1215_);
v_a_1286_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1227_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1227_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1294_, lean_object* v_pre_1295_, lean_object* v_e_1296_, lean_object* v_post_1297_, lean_object* v_usedLetOnly_1298_, lean_object* v_skipConstInApp_1299_, lean_object* v_skipInstances_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
uint8_t v_usedLetOnly_boxed_1307_; uint8_t v_skipConstInApp_boxed_1308_; uint8_t v_skipInstances_boxed_1309_; lean_object* v_res_1310_; 
v_usedLetOnly_boxed_1307_ = lean_unbox(v_usedLetOnly_1298_);
v_skipConstInApp_boxed_1308_ = lean_unbox(v_skipConstInApp_1299_);
v_skipInstances_boxed_1309_ = lean_unbox(v_skipInstances_1300_);
v_res_1310_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(v___x_1294_, v_pre_1295_, v_e_1296_, v_post_1297_, v_usedLetOnly_boxed_1307_, v_skipConstInApp_boxed_1308_, v_skipInstances_boxed_1309_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(lean_object* v_pre_1311_, lean_object* v_post_1312_, uint8_t v_usedLetOnly_1313_, uint8_t v_skipConstInApp_1314_, uint8_t v_skipInstances_1315_, lean_object* v_e_1316_, lean_object* v_a_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_inc(v_a_1317_);
v___x_1323_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1323_, 0, lean_box(0));
lean_closure_set(v___x_1323_, 1, lean_box(0));
lean_closure_set(v___x_1323_, 2, v_a_1317_);
v___x_1324_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v___x_1323_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1359_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1359_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1359_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_a_1325_, v_e_1316_);
lean_dec(v_a_1325_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___f_1334_; lean_object* v___x_1335_; 
lean_del_object(v___x_1327_);
v___x_1330_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0));
v___x_1331_ = lean_box(v_usedLetOnly_1313_);
v___x_1332_ = lean_box(v_skipConstInApp_1314_);
v___x_1333_ = lean_box(v_skipInstances_1315_);
lean_inc_ref(v_e_1316_);
v___f_1334_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed), 13, 7);
lean_closure_set(v___f_1334_, 0, v___x_1330_);
lean_closure_set(v___f_1334_, 1, v_pre_1311_);
lean_closure_set(v___f_1334_, 2, v_e_1316_);
lean_closure_set(v___f_1334_, 3, v_post_1312_);
lean_closure_set(v___f_1334_, 4, v___x_1331_);
lean_closure_set(v___f_1334_, 5, v___x_1332_);
lean_closure_set(v___f_1334_, 6, v___x_1333_);
v___x_1335_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v___f_1334_, v_a_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___f_1337_; lean_object* v___x_1338_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc_n(v_a_1336_, 2);
lean_dec_ref_known(v___x_1335_, 1);
lean_inc(v_a_1317_);
v___f_1337_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1337_, 0, v_a_1317_);
lean_closure_set(v___f_1337_, 1, v_e_1316_);
lean_closure_set(v___f_1337_, 2, v_a_1336_);
v___x_1338_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v___f_1337_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1345_ == 0)
{
lean_object* v_unused_1346_; 
v_unused_1346_ = lean_ctor_get(v___x_1338_, 0);
lean_dec(v_unused_1346_);
v___x_1340_ = v___x_1338_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_dec(v___x_1338_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v_a_1336_);
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1336_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
else
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
lean_dec(v_a_1336_);
v_a_1347_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___x_1338_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1338_);
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
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_dec_ref(v_e_1316_);
return v___x_1335_;
}
}
else
{
lean_object* v_val_1355_; lean_object* v___x_1357_; 
lean_dec_ref(v_e_1316_);
lean_dec_ref(v_post_1312_);
lean_dec_ref(v_pre_1311_);
v_val_1355_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_val_1355_);
lean_dec_ref_known(v___x_1329_, 1);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v_val_1355_);
v___x_1357_ = v___x_1327_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_val_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec_ref(v_e_1316_);
lean_dec_ref(v_post_1312_);
lean_dec_ref(v_pre_1311_);
v_a_1360_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1324_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1324_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed(lean_object* v_fvars_1368_, lean_object* v_pre_1369_, lean_object* v_post_1370_, lean_object* v_usedLetOnly_1371_, lean_object* v_skipConstInApp_1372_, lean_object* v_skipInstances_1373_, lean_object* v_body_1374_, lean_object* v_x_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
uint8_t v_usedLetOnly_boxed_1382_; uint8_t v_skipConstInApp_boxed_1383_; uint8_t v_skipInstances_boxed_1384_; lean_object* v_res_1385_; 
v_usedLetOnly_boxed_1382_ = lean_unbox(v_usedLetOnly_1371_);
v_skipConstInApp_boxed_1383_ = lean_unbox(v_skipConstInApp_1372_);
v_skipInstances_boxed_1384_ = lean_unbox(v_skipInstances_1373_);
v_res_1385_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(v_fvars_1368_, v_pre_1369_, v_post_1370_, v_usedLetOnly_boxed_1382_, v_skipConstInApp_boxed_1383_, v_skipInstances_boxed_1384_, v_body_1374_, v_x_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec(v___y_1376_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(lean_object* v_pre_1386_, lean_object* v_post_1387_, uint8_t v_usedLetOnly_1388_, uint8_t v_skipConstInApp_1389_, uint8_t v_skipInstances_1390_, lean_object* v_fvars_1391_, lean_object* v_e_1392_, lean_object* v_a_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
if (lean_obj_tag(v_e_1392_) == 7)
{
lean_object* v_binderName_1399_; lean_object* v_binderType_1400_; lean_object* v_body_1401_; uint8_t v_binderInfo_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v_binderName_1399_ = lean_ctor_get(v_e_1392_, 0);
lean_inc(v_binderName_1399_);
v_binderType_1400_ = lean_ctor_get(v_e_1392_, 1);
lean_inc_ref(v_binderType_1400_);
v_body_1401_ = lean_ctor_get(v_e_1392_, 2);
lean_inc_ref(v_body_1401_);
v_binderInfo_1402_ = lean_ctor_get_uint8(v_e_1392_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1392_, 3);
v___x_1403_ = lean_expr_instantiate_rev(v_binderType_1400_, v_fvars_1391_);
lean_dec_ref(v_binderType_1400_);
lean_inc_ref(v_post_1387_);
lean_inc_ref(v_pre_1386_);
v___x_1404_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1386_, v_post_1387_, v_usedLetOnly_1388_, v_skipConstInApp_1389_, v_skipInstances_1390_, v___x_1403_, v_a_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___f_1409_; uint8_t v___x_1410_; lean_object* v___x_1411_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref_known(v___x_1404_, 1);
v___x_1406_ = lean_box(v_usedLetOnly_1388_);
v___x_1407_ = lean_box(v_skipConstInApp_1389_);
v___x_1408_ = lean_box(v_skipInstances_1390_);
v___f_1409_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1409_, 0, v_fvars_1391_);
lean_closure_set(v___f_1409_, 1, v_pre_1386_);
lean_closure_set(v___f_1409_, 2, v_post_1387_);
lean_closure_set(v___f_1409_, 3, v___x_1406_);
lean_closure_set(v___f_1409_, 4, v___x_1407_);
lean_closure_set(v___f_1409_, 5, v___x_1408_);
lean_closure_set(v___f_1409_, 6, v_body_1401_);
v___x_1410_ = 0;
v___x_1411_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_1399_, v_binderInfo_1402_, v_a_1405_, v___f_1409_, v___x_1410_, v_a_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1411_;
}
else
{
lean_dec_ref(v_body_1401_);
lean_dec(v_binderName_1399_);
lean_dec_ref(v_fvars_1391_);
lean_dec_ref(v_post_1387_);
lean_dec_ref(v_pre_1386_);
return v___x_1404_;
}
}
else
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = lean_expr_instantiate_rev(v_e_1392_, v_fvars_1391_);
lean_dec_ref(v_e_1392_);
lean_inc_ref(v_post_1387_);
lean_inc_ref(v_pre_1386_);
v___x_1413_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1386_, v_post_1387_, v_usedLetOnly_1388_, v_skipConstInApp_1389_, v_skipInstances_1390_, v___x_1412_, v_a_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; uint8_t v___x_1415_; uint8_t v___x_1416_; uint8_t v___x_1417_; lean_object* v___x_1418_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref_known(v___x_1413_, 1);
v___x_1415_ = 0;
v___x_1416_ = 1;
v___x_1417_ = 1;
v___x_1418_ = l_Lean_Meta_mkForallFVars(v_fvars_1391_, v_a_1414_, v___x_1415_, v_usedLetOnly_1388_, v___x_1416_, v___x_1417_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec_ref(v_fvars_1391_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1420_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref_known(v___x_1418_, 1);
v___x_1420_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1386_, v_post_1387_, v_usedLetOnly_1388_, v_skipConstInApp_1389_, v_skipInstances_1390_, v_a_1419_, v_a_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1420_;
}
else
{
lean_dec_ref(v_post_1387_);
lean_dec_ref(v_pre_1386_);
return v___x_1418_;
}
}
else
{
lean_dec_ref(v_fvars_1391_);
lean_dec_ref(v_post_1387_);
lean_dec_ref(v_pre_1386_);
return v___x_1413_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(lean_object* v_fvars_1421_, lean_object* v_pre_1422_, lean_object* v_post_1423_, uint8_t v_usedLetOnly_1424_, uint8_t v_skipConstInApp_1425_, uint8_t v_skipInstances_1426_, lean_object* v_body_1427_, lean_object* v_x_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = lean_array_push(v_fvars_1421_, v_x_1428_);
v___x_1436_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1422_, v_post_1423_, v_usedLetOnly_1424_, v_skipConstInApp_1425_, v_skipInstances_1426_, v___x_1435_, v_body_1427_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1437_, lean_object* v_post_1438_, lean_object* v_usedLetOnly_1439_, lean_object* v_skipConstInApp_1440_, lean_object* v_skipInstances_1441_, lean_object* v_e_1442_, lean_object* v_a_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
uint8_t v_usedLetOnly_boxed_1449_; uint8_t v_skipConstInApp_boxed_1450_; uint8_t v_skipInstances_boxed_1451_; lean_object* v_res_1452_; 
v_usedLetOnly_boxed_1449_ = lean_unbox(v_usedLetOnly_1439_);
v_skipConstInApp_boxed_1450_ = lean_unbox(v_skipConstInApp_1440_);
v_skipInstances_boxed_1451_ = lean_unbox(v_skipInstances_1441_);
v_res_1452_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1437_, v_post_1438_, v_usedLetOnly_boxed_1449_, v_skipConstInApp_boxed_1450_, v_skipInstances_boxed_1451_, v_e_1442_, v_a_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v_a_1443_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1453_, lean_object* v_post_1454_, lean_object* v_usedLetOnly_1455_, lean_object* v_skipConstInApp_1456_, lean_object* v_skipInstances_1457_, lean_object* v_sz_1458_, lean_object* v_i_1459_, lean_object* v_bs_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
uint8_t v_usedLetOnly_boxed_1467_; uint8_t v_skipConstInApp_boxed_1468_; uint8_t v_skipInstances_boxed_1469_; size_t v_sz_boxed_1470_; size_t v_i_boxed_1471_; lean_object* v_res_1472_; 
v_usedLetOnly_boxed_1467_ = lean_unbox(v_usedLetOnly_1455_);
v_skipConstInApp_boxed_1468_ = lean_unbox(v_skipConstInApp_1456_);
v_skipInstances_boxed_1469_ = lean_unbox(v_skipInstances_1457_);
v_sz_boxed_1470_ = lean_unbox_usize(v_sz_1458_);
lean_dec(v_sz_1458_);
v_i_boxed_1471_ = lean_unbox_usize(v_i_1459_);
lean_dec(v_i_1459_);
v_res_1472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_pre_1453_, v_post_1454_, v_usedLetOnly_boxed_1467_, v_skipConstInApp_boxed_1468_, v_skipInstances_boxed_1469_, v_sz_boxed_1470_, v_i_boxed_1471_, v_bs_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___boxed(lean_object* v_pre_1473_, lean_object* v_post_1474_, lean_object* v_usedLetOnly_1475_, lean_object* v_skipConstInApp_1476_, lean_object* v_skipInstances_1477_, lean_object* v_e_1478_, lean_object* v_a_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
uint8_t v_usedLetOnly_boxed_1485_; uint8_t v_skipConstInApp_boxed_1486_; uint8_t v_skipInstances_boxed_1487_; lean_object* v_res_1488_; 
v_usedLetOnly_boxed_1485_ = lean_unbox(v_usedLetOnly_1475_);
v_skipConstInApp_boxed_1486_ = lean_unbox(v_skipConstInApp_1476_);
v_skipInstances_boxed_1487_ = lean_unbox(v_skipInstances_1477_);
v_res_1488_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1473_, v_post_1474_, v_usedLetOnly_boxed_1485_, v_skipConstInApp_boxed_1486_, v_skipInstances_boxed_1487_, v_e_1478_, v_a_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v_a_1479_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___boxed(lean_object* v_pre_1489_, lean_object* v_post_1490_, lean_object* v_usedLetOnly_1491_, lean_object* v_skipConstInApp_1492_, lean_object* v_skipInstances_1493_, lean_object* v_fvars_1494_, lean_object* v_e_1495_, lean_object* v_a_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
uint8_t v_usedLetOnly_boxed_1502_; uint8_t v_skipConstInApp_boxed_1503_; uint8_t v_skipInstances_boxed_1504_; lean_object* v_res_1505_; 
v_usedLetOnly_boxed_1502_ = lean_unbox(v_usedLetOnly_1491_);
v_skipConstInApp_boxed_1503_ = lean_unbox(v_skipConstInApp_1492_);
v_skipInstances_boxed_1504_ = lean_unbox(v_skipInstances_1493_);
v_res_1505_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1489_, v_post_1490_, v_usedLetOnly_boxed_1502_, v_skipConstInApp_boxed_1503_, v_skipInstances_boxed_1504_, v_fvars_1494_, v_e_1495_, v_a_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v_a_1496_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___boxed(lean_object* v_pre_1506_, lean_object* v_post_1507_, lean_object* v_usedLetOnly_1508_, lean_object* v_skipConstInApp_1509_, lean_object* v_skipInstances_1510_, lean_object* v_fvars_1511_, lean_object* v_e_1512_, lean_object* v_a_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
uint8_t v_usedLetOnly_boxed_1519_; uint8_t v_skipConstInApp_boxed_1520_; uint8_t v_skipInstances_boxed_1521_; lean_object* v_res_1522_; 
v_usedLetOnly_boxed_1519_ = lean_unbox(v_usedLetOnly_1508_);
v_skipConstInApp_boxed_1520_ = lean_unbox(v_skipConstInApp_1509_);
v_skipInstances_boxed_1521_ = lean_unbox(v_skipInstances_1510_);
v_res_1522_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_1506_, v_post_1507_, v_usedLetOnly_boxed_1519_, v_skipConstInApp_boxed_1520_, v_skipInstances_boxed_1521_, v_fvars_1511_, v_e_1512_, v_a_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v_a_1513_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___boxed(lean_object* v_pre_1523_, lean_object* v_post_1524_, lean_object* v_usedLetOnly_1525_, lean_object* v_skipConstInApp_1526_, lean_object* v_skipInstances_1527_, lean_object* v_fvars_1528_, lean_object* v_e_1529_, lean_object* v_a_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
uint8_t v_usedLetOnly_boxed_1536_; uint8_t v_skipConstInApp_boxed_1537_; uint8_t v_skipInstances_boxed_1538_; lean_object* v_res_1539_; 
v_usedLetOnly_boxed_1536_ = lean_unbox(v_usedLetOnly_1525_);
v_skipConstInApp_boxed_1537_ = lean_unbox(v_skipConstInApp_1526_);
v_skipInstances_boxed_1538_ = lean_unbox(v_skipInstances_1527_);
v_res_1539_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_1523_, v_post_1524_, v_usedLetOnly_boxed_1536_, v_skipConstInApp_boxed_1537_, v_skipInstances_boxed_1538_, v_fvars_1528_, v_e_1529_, v_a_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v_a_1530_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_upperBound_1540_, lean_object* v___x_1541_, lean_object* v_pre_1542_, lean_object* v_post_1543_, lean_object* v_usedLetOnly_1544_, lean_object* v_skipConstInApp_1545_, lean_object* v_skipInstances_1546_, lean_object* v_a_1547_, lean_object* v_b_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
uint8_t v_usedLetOnly_boxed_1555_; uint8_t v_skipConstInApp_boxed_1556_; uint8_t v_skipInstances_boxed_1557_; lean_object* v_res_1558_; 
v_usedLetOnly_boxed_1555_ = lean_unbox(v_usedLetOnly_1544_);
v_skipConstInApp_boxed_1556_ = lean_unbox(v_skipConstInApp_1545_);
v_skipInstances_boxed_1557_ = lean_unbox(v_skipInstances_1546_);
v_res_1558_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v_upperBound_1540_, v___x_1541_, v_pre_1542_, v_post_1543_, v_usedLetOnly_boxed_1555_, v_skipConstInApp_boxed_1556_, v_skipInstances_boxed_1557_, v_a_1547_, v_b_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___x_1541_);
lean_dec(v_upperBound_1540_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8___boxed(lean_object* v_skipInstances_1559_, lean_object* v_pre_1560_, lean_object* v_post_1561_, lean_object* v_usedLetOnly_1562_, lean_object* v_skipConstInApp_1563_, lean_object* v_x_1564_, lean_object* v_x_1565_, lean_object* v_x_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
uint8_t v_skipInstances_boxed_1573_; uint8_t v_usedLetOnly_boxed_1574_; uint8_t v_skipConstInApp_boxed_1575_; lean_object* v_res_1576_; 
v_skipInstances_boxed_1573_ = lean_unbox(v_skipInstances_1559_);
v_usedLetOnly_boxed_1574_ = lean_unbox(v_usedLetOnly_1562_);
v_skipConstInApp_boxed_1575_ = lean_unbox(v_skipConstInApp_1563_);
v_res_1576_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_boxed_1573_, v_pre_1560_, v_post_1561_, v_usedLetOnly_boxed_1574_, v_skipConstInApp_boxed_1575_, v_x_1564_, v_x_1565_, v_x_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
return v_res_1576_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1577_ = lean_box(0);
v___x_1578_ = lean_unsigned_to_nat(16u);
v___x_1579_ = lean_mk_array(v___x_1578_, v___x_1577_);
return v___x_1579_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1580_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0);
v___x_1581_ = lean_unsigned_to_nat(0u);
v___x_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
lean_ctor_set(v___x_1582_, 1, v___x_1580_);
return v___x_1582_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_1584_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1584_, 0, lean_box(0));
lean_closure_set(v___x_1584_, 1, lean_box(0));
lean_closure_set(v___x_1584_, 2, v___x_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(lean_object* v_input_1585_, lean_object* v_pre_1586_, lean_object* v_post_1587_, uint8_t v_usedLetOnly_1588_, uint8_t v_skipConstInApp_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v_a_1597_; uint8_t v___x_1598_; lean_object* v___x_1599_; 
v___x_1595_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
v___x_1596_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v___x_1595_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_a_1597_);
lean_dec_ref(v___x_1596_);
v___x_1598_ = 0;
v___x_1599_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1586_, v_post_1587_, v_usedLetOnly_1588_, v_skipConstInApp_1589_, v___x_1598_, v_input_1585_, v_a_1597_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1600_);
lean_dec_ref_known(v___x_1599_, 1);
v___x_1601_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1601_, 0, lean_box(0));
lean_closure_set(v___x_1601_, 1, lean_box(0));
lean_closure_set(v___x_1601_, 2, v_a_1597_);
v___x_1602_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v___x_1601_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1609_ == 0)
{
lean_object* v_unused_1610_; 
v_unused_1610_ = lean_ctor_get(v___x_1602_, 0);
lean_dec(v_unused_1610_);
v___x_1604_ = v___x_1602_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_dec(v___x_1602_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v_a_1600_);
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1600_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
else
{
lean_dec(v_a_1597_);
return v___x_1599_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___boxed(lean_object* v_input_1611_, lean_object* v_pre_1612_, lean_object* v_post_1613_, lean_object* v_usedLetOnly_1614_, lean_object* v_skipConstInApp_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
uint8_t v_usedLetOnly_boxed_1621_; uint8_t v_skipConstInApp_boxed_1622_; lean_object* v_res_1623_; 
v_usedLetOnly_boxed_1621_ = lean_unbox(v_usedLetOnly_1614_);
v_skipConstInApp_boxed_1622_ = lean_unbox(v_skipConstInApp_1615_);
v_res_1623_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_input_1611_, v_pre_1612_, v_post_1613_, v_usedLetOnly_boxed_1621_, v_skipConstInApp_boxed_1622_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object* v_e_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_){
_start:
{
lean_object* v___x_1632_; lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1645_; 
v___x_1632_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_1626_, v_a_1630_);
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1635_ = v___x_1632_;
v_isShared_1636_ = v_isSharedCheck_1645_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1632_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1645_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
uint8_t v___x_1637_; 
v___x_1637_ = lean_unbox(v_a_1633_);
lean_dec(v_a_1633_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1639_; 
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v_e_1626_);
v___x_1639_ = v___x_1635_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_e_1626_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
else
{
lean_object* v___f_1641_; uint8_t v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_del_object(v___x_1635_);
v___f_1641_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducible___closed__0));
v___x_1642_ = 0;
v___x_1643_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducible___closed__1));
v___x_1644_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_e_1626_, v___x_1643_, v___f_1641_, v___x_1642_, v___x_1642_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
return v___x_1644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___boxed(lean_object* v_e_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lean_Meta_Sym_unfoldReducible(v_e_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(lean_object* v_upperBound_1653_, lean_object* v___x_1654_, lean_object* v_pre_1655_, lean_object* v_post_1656_, uint8_t v_usedLetOnly_1657_, uint8_t v_skipConstInApp_1658_, uint8_t v_skipInstances_1659_, lean_object* v___x_1660_, lean_object* v_inst_1661_, lean_object* v_R_1662_, lean_object* v_a_1663_, lean_object* v_b_1664_, lean_object* v_c_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v_upperBound_1653_, v___x_1654_, v_pre_1655_, v_post_1656_, v_usedLetOnly_1657_, v_skipConstInApp_1658_, v_skipInstances_1659_, v_a_1663_, v_b_1664_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_1673_ = _args[0];
lean_object* v___x_1674_ = _args[1];
lean_object* v_pre_1675_ = _args[2];
lean_object* v_post_1676_ = _args[3];
lean_object* v_usedLetOnly_1677_ = _args[4];
lean_object* v_skipConstInApp_1678_ = _args[5];
lean_object* v_skipInstances_1679_ = _args[6];
lean_object* v___x_1680_ = _args[7];
lean_object* v_inst_1681_ = _args[8];
lean_object* v_R_1682_ = _args[9];
lean_object* v_a_1683_ = _args[10];
lean_object* v_b_1684_ = _args[11];
lean_object* v_c_1685_ = _args[12];
lean_object* v___y_1686_ = _args[13];
lean_object* v___y_1687_ = _args[14];
lean_object* v___y_1688_ = _args[15];
lean_object* v___y_1689_ = _args[16];
lean_object* v___y_1690_ = _args[17];
lean_object* v___y_1691_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_1692_; uint8_t v_skipConstInApp_boxed_1693_; uint8_t v_skipInstances_boxed_1694_; lean_object* v_res_1695_; 
v_usedLetOnly_boxed_1692_ = lean_unbox(v_usedLetOnly_1677_);
v_skipConstInApp_boxed_1693_ = lean_unbox(v_skipConstInApp_1678_);
v_skipInstances_boxed_1694_ = lean_unbox(v_skipInstances_1679_);
v_res_1695_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_upperBound_1673_, v___x_1674_, v_pre_1675_, v_post_1676_, v_usedLetOnly_boxed_1692_, v_skipConstInApp_boxed_1693_, v_skipInstances_boxed_1694_, v___x_1680_, v_inst_1681_, v_R_1682_, v_a_1683_, v_b_1684_, v_c_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec(v___x_1680_);
lean_dec_ref(v___x_1674_);
lean_dec(v_upperBound_1673_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_1696_, lean_object* v_m_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_m_1697_, v_a_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_1700_, lean_object* v_m_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(v_00_u03b2_1700_, v_m_1701_, v_a_1702_);
lean_dec_ref(v_a_1702_);
lean_dec_ref(v_m_1701_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1704_, lean_object* v_name_1705_, uint8_t v_bi_1706_, lean_object* v_type_1707_, lean_object* v_k_1708_, uint8_t v_kind_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_1705_, v_bi_1706_, v_type_1707_, v_k_1708_, v_kind_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1717_, lean_object* v_name_1718_, lean_object* v_bi_1719_, lean_object* v_type_1720_, lean_object* v_k_1721_, lean_object* v_kind_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
uint8_t v_bi_boxed_1729_; uint8_t v_kind_boxed_1730_; lean_object* v_res_1731_; 
v_bi_boxed_1729_ = lean_unbox(v_bi_1719_);
v_kind_boxed_1730_ = lean_unbox(v_kind_1722_);
v_res_1731_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1717_, v_name_1718_, v_bi_boxed_1729_, v_type_1720_, v_k_1721_, v_kind_boxed_1730_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(lean_object* v_00_u03b1_1732_, lean_object* v_name_1733_, lean_object* v_type_1734_, lean_object* v_val_1735_, lean_object* v_k_1736_, uint8_t v_nondep_1737_, uint8_t v_kind_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_1733_, v_type_1734_, v_val_1735_, v_k_1736_, v_nondep_1737_, v_kind_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1746_, lean_object* v_name_1747_, lean_object* v_type_1748_, lean_object* v_val_1749_, lean_object* v_k_1750_, lean_object* v_nondep_1751_, lean_object* v_kind_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
uint8_t v_nondep_boxed_1759_; uint8_t v_kind_boxed_1760_; lean_object* v_res_1761_; 
v_nondep_boxed_1759_ = lean_unbox(v_nondep_1751_);
v_kind_boxed_1760_ = lean_unbox(v_kind_1752_);
v_res_1761_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_1746_, v_name_1747_, v_type_1748_, v_val_1749_, v_k_1750_, v_nondep_boxed_1759_, v_kind_boxed_1760_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(lean_object* v_00_u03b1_1762_, lean_object* v_ref_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1763_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___boxed(lean_object* v_00_u03b1_1770_, lean_object* v_ref_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_1770_, v_ref_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(lean_object* v_00_u03b1_1778_, lean_object* v_x_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___boxed(lean_object* v_00_u03b1_1787_, lean_object* v_x_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(v_00_u03b1_1787_, v_x_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10(lean_object* v_00_u03b2_1796_, lean_object* v_m_1797_, lean_object* v_a_1798_, lean_object* v_b_1799_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v_m_1797_, v_a_1798_, v_b_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(lean_object* v_00_u03b2_1801_, lean_object* v_a_1802_, lean_object* v_x_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1802_, v_x_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_00_u03b2_1805_, lean_object* v_a_1806_, lean_object* v_x_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_1805_, v_a_1806_, v_x_1807_);
lean_dec(v_x_1807_);
lean_dec_ref(v_a_1806_);
return v_res_1808_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(lean_object* v_00_u03b2_1809_, lean_object* v_a_1810_, lean_object* v_x_1811_){
_start:
{
uint8_t v___x_1812_; 
v___x_1812_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_1810_, v_x_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___boxed(lean_object* v_00_u03b2_1813_, lean_object* v_a_1814_, lean_object* v_x_1815_){
_start:
{
uint8_t v_res_1816_; lean_object* v_r_1817_; 
v_res_1816_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_1813_, v_a_1814_, v_x_1815_);
lean_dec(v_x_1815_);
lean_dec_ref(v_a_1814_);
v_r_1817_ = lean_box(v_res_1816_);
return v_r_1817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16(lean_object* v_00_u03b2_1818_, lean_object* v_data_1819_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(v_data_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17(lean_object* v_00_u03b2_1821_, lean_object* v_a_1822_, lean_object* v_b_1823_, lean_object* v_x_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_1822_, v_b_1823_, v_x_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object* v_00_u03b2_1826_, lean_object* v_i_1827_, lean_object* v_source_1828_, lean_object* v_target_1829_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_1827_, v_source_1828_, v_target_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object* v_00_u03b2_1831_, lean_object* v_x_1832_, lean_object* v_x_1833_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_1832_, v_x_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(lean_object* v_msgData_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v___x_1841_; lean_object* v_env_1842_; lean_object* v___x_1843_; lean_object* v_mctx_1844_; lean_object* v_lctx_1845_; lean_object* v_options_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1841_ = lean_st_ref_get(v___y_1839_);
v_env_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc_ref(v_env_1842_);
lean_dec(v___x_1841_);
v___x_1843_ = lean_st_ref_get(v___y_1837_);
v_mctx_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc_ref(v_mctx_1844_);
lean_dec(v___x_1843_);
v_lctx_1845_ = lean_ctor_get(v___y_1836_, 2);
v_options_1846_ = lean_ctor_get(v___y_1838_, 2);
lean_inc_ref(v_options_1846_);
lean_inc_ref(v_lctx_1845_);
v___x_1847_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1847_, 0, v_env_1842_);
lean_ctor_set(v___x_1847_, 1, v_mctx_1844_);
lean_ctor_set(v___x_1847_, 2, v_lctx_1845_);
lean_ctor_set(v___x_1847_, 3, v_options_1846_);
v___x_1848_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
lean_ctor_set(v___x_1848_, 1, v_msgData_1835_);
v___x_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0___boxed(lean_object* v_msgData_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msgData_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
return v_res_1856_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1857_; double v___x_1858_; 
v___x_1857_ = lean_unsigned_to_nat(0u);
v___x_1858_ = lean_float_of_nat(v___x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(lean_object* v_cls_1862_, lean_object* v_msg_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_ref_1869_; lean_object* v___x_1870_; lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1915_; 
v_ref_1869_ = lean_ctor_get(v___y_1866_, 5);
v___x_1870_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1873_ = v___x_1870_;
v_isShared_1874_ = v_isSharedCheck_1915_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1915_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; lean_object* v_traceState_1876_; lean_object* v_env_1877_; lean_object* v_nextMacroScope_1878_; lean_object* v_ngen_1879_; lean_object* v_auxDeclNGen_1880_; lean_object* v_cache_1881_; lean_object* v_messages_1882_; lean_object* v_infoState_1883_; lean_object* v_snapshotTasks_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1914_; 
v___x_1875_ = lean_st_ref_take(v___y_1867_);
v_traceState_1876_ = lean_ctor_get(v___x_1875_, 4);
v_env_1877_ = lean_ctor_get(v___x_1875_, 0);
v_nextMacroScope_1878_ = lean_ctor_get(v___x_1875_, 1);
v_ngen_1879_ = lean_ctor_get(v___x_1875_, 2);
v_auxDeclNGen_1880_ = lean_ctor_get(v___x_1875_, 3);
v_cache_1881_ = lean_ctor_get(v___x_1875_, 5);
v_messages_1882_ = lean_ctor_get(v___x_1875_, 6);
v_infoState_1883_ = lean_ctor_get(v___x_1875_, 7);
v_snapshotTasks_1884_ = lean_ctor_get(v___x_1875_, 8);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1886_ = v___x_1875_;
v_isShared_1887_ = v_isSharedCheck_1914_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_snapshotTasks_1884_);
lean_inc(v_infoState_1883_);
lean_inc(v_messages_1882_);
lean_inc(v_cache_1881_);
lean_inc(v_traceState_1876_);
lean_inc(v_auxDeclNGen_1880_);
lean_inc(v_ngen_1879_);
lean_inc(v_nextMacroScope_1878_);
lean_inc(v_env_1877_);
lean_dec(v___x_1875_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1914_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
uint64_t v_tid_1888_; lean_object* v_traces_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1913_; 
v_tid_1888_ = lean_ctor_get_uint64(v_traceState_1876_, sizeof(void*)*1);
v_traces_1889_ = lean_ctor_get(v_traceState_1876_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v_traceState_1876_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1891_ = v_traceState_1876_;
v_isShared_1892_ = v_isSharedCheck_1913_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_traces_1889_);
lean_dec(v_traceState_1876_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1913_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; double v___x_1894_; uint8_t v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1893_ = lean_box(0);
v___x_1894_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_1895_ = 0;
v___x_1896_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_1897_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1897_, 0, v_cls_1862_);
lean_ctor_set(v___x_1897_, 1, v___x_1893_);
lean_ctor_set(v___x_1897_, 2, v___x_1896_);
lean_ctor_set_float(v___x_1897_, sizeof(void*)*3, v___x_1894_);
lean_ctor_set_float(v___x_1897_, sizeof(void*)*3 + 8, v___x_1894_);
lean_ctor_set_uint8(v___x_1897_, sizeof(void*)*3 + 16, v___x_1895_);
v___x_1898_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
v___x_1899_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1897_);
lean_ctor_set(v___x_1899_, 1, v_a_1871_);
lean_ctor_set(v___x_1899_, 2, v___x_1898_);
lean_inc(v_ref_1869_);
v___x_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1900_, 0, v_ref_1869_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = l_Lean_PersistentArray_push___redArg(v_traces_1889_, v___x_1900_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v___x_1901_);
v___x_1903_ = v___x_1891_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1901_);
lean_ctor_set_uint64(v_reuseFailAlloc_1912_, sizeof(void*)*1, v_tid_1888_);
v___x_1903_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_object* v___x_1905_; 
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 4, v___x_1903_);
v___x_1905_ = v___x_1886_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_env_1877_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v_nextMacroScope_1878_);
lean_ctor_set(v_reuseFailAlloc_1911_, 2, v_ngen_1879_);
lean_ctor_set(v_reuseFailAlloc_1911_, 3, v_auxDeclNGen_1880_);
lean_ctor_set(v_reuseFailAlloc_1911_, 4, v___x_1903_);
lean_ctor_set(v_reuseFailAlloc_1911_, 5, v_cache_1881_);
lean_ctor_set(v_reuseFailAlloc_1911_, 6, v_messages_1882_);
lean_ctor_set(v_reuseFailAlloc_1911_, 7, v_infoState_1883_);
lean_ctor_set(v_reuseFailAlloc_1911_, 8, v_snapshotTasks_1884_);
v___x_1905_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1906_ = lean_st_ref_set(v___y_1867_, v___x_1905_);
v___x_1907_ = lean_box(0);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v___x_1907_);
v___x_1909_ = v___x_1873_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___boxed(lean_object* v_cls_1916_, lean_object* v_msg_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v_cls_1916_, v_msg_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
return v_res_1923_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1927_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_1928_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__1));
v___x_1929_ = l_Lean_Name_append(v___x_1928_, v___x_1927_);
return v___x_1929_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__3));
v___x_1932_ = l_Lean_stringToMessageData(v___x_1931_);
return v___x_1932_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__5));
v___x_1935_ = l_Lean_stringToMessageData(v___x_1934_);
return v___x_1935_;
}
}
static uint64_t _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__7(void){
_start:
{
uint8_t v___x_1936_; uint64_t v___x_1937_; 
v___x_1936_ = 1;
v___x_1937_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1936_);
return v___x_1937_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__8));
v___x_1940_ = l_Lean_stringToMessageData(v___x_1939_);
return v___x_1940_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__11(void){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__10));
v___x_1943_ = l_Lean_stringToMessageData(v___x_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0(lean_object* v_e_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
if (lean_obj_tag(v_e_1944_) == 11)
{
lean_object* v_typeName_1956_; lean_object* v_idx_1957_; lean_object* v_struct_1958_; lean_object* v___x_1959_; lean_object* v_env_1960_; lean_object* v___x_1961_; 
v_typeName_1956_ = lean_ctor_get(v_e_1944_, 0);
v_idx_1957_ = lean_ctor_get(v_e_1944_, 1);
v_struct_1958_ = lean_ctor_get(v_e_1944_, 2);
v___x_1959_ = lean_st_ref_get(v___y_1948_);
v_env_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc_ref(v_env_1960_);
lean_dec(v___x_1959_);
lean_inc(v_typeName_1956_);
v___x_1961_ = l_Lean_getStructureInfo_x3f(v_env_1960_, v_typeName_1956_);
if (lean_obj_tag(v___x_1961_) == 1)
{
lean_object* v_val_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_2061_; 
v_val_1962_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_1964_ = v___x_1961_;
v_isShared_1965_ = v_isSharedCheck_2061_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_val_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_2061_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v_fieldNames_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v_fieldNames_1966_ = lean_ctor_get(v_val_1962_, 1);
lean_inc_ref(v_fieldNames_1966_);
lean_dec(v_val_1962_);
v___x_1967_ = lean_array_get_size(v_fieldNames_1966_);
v___x_1968_ = lean_nat_dec_lt(v_idx_1957_, v___x_1967_);
if (v___x_1968_ == 0)
{
lean_object* v_options_1969_; uint8_t v_hasTrace_1970_; 
lean_dec_ref(v_fieldNames_1966_);
v_options_1969_ = lean_ctor_get(v___y_1947_, 2);
v_hasTrace_1970_ = lean_ctor_get_uint8(v_options_1969_, sizeof(void*)*1);
if (v_hasTrace_1970_ == 0)
{
lean_del_object(v___x_1964_);
goto v___jp_1950_;
}
else
{
lean_object* v_inheritedTraceOptions_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; 
v_inheritedTraceOptions_1971_ = lean_ctor_get(v___y_1947_, 13);
v___x_1972_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_1973_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__2);
v___x_1974_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1971_, v_options_1969_, v___x_1973_);
if (v___x_1974_ == 0)
{
lean_del_object(v___x_1964_);
goto v___jp_1950_;
}
else
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1978_; 
v___x_1975_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__4, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__4_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__4);
lean_inc(v_idx_1957_);
v___x_1976_ = l_Nat_reprFast(v_idx_1957_);
if (v_isShared_1965_ == 0)
{
lean_ctor_set_tag(v___x_1964_, 3);
lean_ctor_set(v___x_1964_, 0, v___x_1976_);
v___x_1978_ = v___x_1964_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1979_ = l_Lean_MessageData_ofFormat(v___x_1978_);
v___x_1980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1975_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
v___x_1981_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__6, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__6_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__6);
v___x_1982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1980_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
lean_inc_ref(v_e_1944_);
v___x_1983_ = l_Lean_indentExpr(v_e_1944_);
v___x_1984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1982_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v___x_1972_, v___x_1984_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_dec_ref_known(v___x_1985_, 1);
goto v___jp_1950_;
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
lean_dec_ref_known(v_e_1944_, 3);
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1985_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1985_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1995_; uint8_t v_foApprox_1996_; uint8_t v_ctxApprox_1997_; uint8_t v_quasiPatternApprox_1998_; uint8_t v_constApprox_1999_; uint8_t v_isDefEqStuckEx_2000_; uint8_t v_unificationHints_2001_; uint8_t v_proofIrrelevance_2002_; uint8_t v_assignSyntheticOpaque_2003_; uint8_t v_offsetCnstrs_2004_; uint8_t v_etaStruct_2005_; uint8_t v_univApprox_2006_; uint8_t v_iota_2007_; uint8_t v_beta_2008_; uint8_t v_proj_2009_; uint8_t v_zeta_2010_; uint8_t v_zetaDelta_2011_; uint8_t v_zetaUnused_2012_; uint8_t v_zetaHave_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2060_; 
lean_inc_ref(v_struct_1958_);
lean_inc(v_idx_1957_);
lean_dec_ref_known(v_e_1944_, 3);
v___x_1995_ = l_Lean_Meta_Context_config(v___y_1945_);
v_foApprox_1996_ = lean_ctor_get_uint8(v___x_1995_, 0);
v_ctxApprox_1997_ = lean_ctor_get_uint8(v___x_1995_, 1);
v_quasiPatternApprox_1998_ = lean_ctor_get_uint8(v___x_1995_, 2);
v_constApprox_1999_ = lean_ctor_get_uint8(v___x_1995_, 3);
v_isDefEqStuckEx_2000_ = lean_ctor_get_uint8(v___x_1995_, 4);
v_unificationHints_2001_ = lean_ctor_get_uint8(v___x_1995_, 5);
v_proofIrrelevance_2002_ = lean_ctor_get_uint8(v___x_1995_, 6);
v_assignSyntheticOpaque_2003_ = lean_ctor_get_uint8(v___x_1995_, 7);
v_offsetCnstrs_2004_ = lean_ctor_get_uint8(v___x_1995_, 8);
v_etaStruct_2005_ = lean_ctor_get_uint8(v___x_1995_, 10);
v_univApprox_2006_ = lean_ctor_get_uint8(v___x_1995_, 11);
v_iota_2007_ = lean_ctor_get_uint8(v___x_1995_, 12);
v_beta_2008_ = lean_ctor_get_uint8(v___x_1995_, 13);
v_proj_2009_ = lean_ctor_get_uint8(v___x_1995_, 14);
v_zeta_2010_ = lean_ctor_get_uint8(v___x_1995_, 15);
v_zetaDelta_2011_ = lean_ctor_get_uint8(v___x_1995_, 16);
v_zetaUnused_2012_ = lean_ctor_get_uint8(v___x_1995_, 17);
v_zetaHave_2013_ = lean_ctor_get_uint8(v___x_1995_, 18);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2015_ = v___x_1995_;
v_isShared_2016_ = v_isSharedCheck_2060_;
goto v_resetjp_2014_;
}
else
{
lean_dec(v___x_1995_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2060_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
uint8_t v_trackZetaDelta_2017_; lean_object* v_zetaDeltaSet_2018_; lean_object* v_lctx_2019_; lean_object* v_localInstances_2020_; lean_object* v_defEqCtx_x3f_2021_; lean_object* v_synthPendingDepth_2022_; lean_object* v_canUnfold_x3f_2023_; uint8_t v_univApprox_2024_; uint8_t v_inTypeClassResolution_2025_; uint8_t v_cacheInferType_2026_; uint8_t v___x_2027_; lean_object* v_config_2029_; 
v_trackZetaDelta_2017_ = lean_ctor_get_uint8(v___y_1945_, sizeof(void*)*7);
v_zetaDeltaSet_2018_ = lean_ctor_get(v___y_1945_, 1);
v_lctx_2019_ = lean_ctor_get(v___y_1945_, 2);
v_localInstances_2020_ = lean_ctor_get(v___y_1945_, 3);
v_defEqCtx_x3f_2021_ = lean_ctor_get(v___y_1945_, 4);
v_synthPendingDepth_2022_ = lean_ctor_get(v___y_1945_, 5);
v_canUnfold_x3f_2023_ = lean_ctor_get(v___y_1945_, 6);
v_univApprox_2024_ = lean_ctor_get_uint8(v___y_1945_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2025_ = lean_ctor_get_uint8(v___y_1945_, sizeof(void*)*7 + 2);
v_cacheInferType_2026_ = lean_ctor_get_uint8(v___y_1945_, sizeof(void*)*7 + 3);
v___x_2027_ = 1;
if (v_isShared_2016_ == 0)
{
v_config_2029_ = v___x_2015_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, 0, v_foApprox_1996_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, 1, v_ctxApprox_1997_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, 2, v_quasiPatternApprox_1998_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, 3, v_constApprox_1999_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, 4, v_isDefEqStuckEx_2000_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, 5, v_unificationHints_2001_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, 6, v_proofIrrelevance_2002_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, 7, v_assignSyntheticOpaque_2003_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, 8, v_offsetCnstrs_2004_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, 10, v_etaStruct_2005_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, 11, v_univApprox_2006_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, 12, v_iota_2007_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, 13, v_beta_2008_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, 14, v_proj_2009_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, 15, v_zeta_2010_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, 16, v_zetaDelta_2011_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, 17, v_zetaUnused_2012_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, 18, v_zetaHave_2013_);
v_config_2029_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
uint64_t v___x_2030_; uint64_t v___x_2031_; uint64_t v___x_2032_; lean_object* v___x_2033_; uint64_t v___x_2034_; uint64_t v___x_2035_; uint64_t v_key_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_ctor_set_uint8(v_config_2029_, 9, v___x_2027_);
v___x_2030_ = l_Lean_Meta_Context_configKey(v___y_1945_);
v___x_2031_ = 3ULL;
v___x_2032_ = lean_uint64_shift_right(v___x_2030_, v___x_2031_);
v___x_2033_ = lean_array_fget(v_fieldNames_1966_, v_idx_1957_);
lean_dec(v_idx_1957_);
lean_dec_ref(v_fieldNames_1966_);
v___x_2034_ = lean_uint64_shift_left(v___x_2032_, v___x_2031_);
v___x_2035_ = lean_uint64_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__7, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__7_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__7);
v_key_2036_ = lean_uint64_lor(v___x_2034_, v___x_2035_);
v___x_2037_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2037_, 0, v_config_2029_);
lean_ctor_set_uint64(v___x_2037_, sizeof(void*)*1, v_key_2036_);
lean_inc(v_canUnfold_x3f_2023_);
lean_inc(v_synthPendingDepth_2022_);
lean_inc(v_defEqCtx_x3f_2021_);
lean_inc_ref(v_localInstances_2020_);
lean_inc_ref(v_lctx_2019_);
lean_inc(v_zetaDeltaSet_2018_);
v___x_2038_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
lean_ctor_set(v___x_2038_, 1, v_zetaDeltaSet_2018_);
lean_ctor_set(v___x_2038_, 2, v_lctx_2019_);
lean_ctor_set(v___x_2038_, 3, v_localInstances_2020_);
lean_ctor_set(v___x_2038_, 4, v_defEqCtx_x3f_2021_);
lean_ctor_set(v___x_2038_, 5, v_synthPendingDepth_2022_);
lean_ctor_set(v___x_2038_, 6, v_canUnfold_x3f_2023_);
lean_ctor_set_uint8(v___x_2038_, sizeof(void*)*7, v_trackZetaDelta_2017_);
lean_ctor_set_uint8(v___x_2038_, sizeof(void*)*7 + 1, v_univApprox_2024_);
lean_ctor_set_uint8(v___x_2038_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2025_);
lean_ctor_set_uint8(v___x_2038_, sizeof(void*)*7 + 3, v_cacheInferType_2026_);
v___x_2039_ = l_Lean_Meta_mkProjection(v_struct_1958_, v___x_2033_, v___x_2038_, v___y_1946_, v___y_1947_, v___y_1948_);
lean_dec_ref_known(v___x_2038_, 7);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2050_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2050_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2050_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 0, v_a_2040_);
v___x_2045_ = v___x_1964_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
lean_object* v___x_2047_; 
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2045_);
v___x_2047_ = v___x_2042_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_del_object(v___x_1964_);
v_a_2051_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2039_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2039_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
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
lean_object* v_options_2062_; uint8_t v_hasTrace_2063_; 
lean_dec(v___x_1961_);
v_options_2062_ = lean_ctor_get(v___y_1947_, 2);
v_hasTrace_2063_ = lean_ctor_get_uint8(v_options_2062_, sizeof(void*)*1);
if (v_hasTrace_2063_ == 0)
{
goto v___jp_1953_;
}
else
{
lean_object* v_inheritedTraceOptions_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; 
v_inheritedTraceOptions_2064_ = lean_ctor_get(v___y_1947_, 13);
v___x_2065_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_2066_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__2);
v___x_2067_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2064_, v_options_2062_, v___x_2066_);
if (v___x_2067_ == 0)
{
goto v___jp_1953_;
}
else
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2068_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__9, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__9);
lean_inc(v_typeName_1956_);
v___x_2069_ = l_Lean_MessageData_ofName(v_typeName_1956_);
v___x_2070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2068_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
v___x_2071_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__11, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__11_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__11);
v___x_2072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2070_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
lean_inc_ref(v_e_1944_);
v___x_2073_ = l_Lean_indentExpr(v_e_1944_);
v___x_2074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2072_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
v___x_2075_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v___x_2065_, v___x_2074_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_dec_ref_known(v___x_2075_, 1);
goto v___jp_1953_;
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec_ref_known(v_e_1944_, 3);
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2075_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2084_, 0, v_e_1944_);
v___x_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
return v___x_2085_;
}
v___jp_1950_:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1951_, 0, v_e_1944_);
v___x_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
return v___x_1952_;
}
v___jp_1953_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1954_, 0, v_e_1944_);
v___x_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
return v___x_1955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___boxed(lean_object* v_e_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_Meta_Sym_foldProjs___lam__0(v_e_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1(lean_object* v_x_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___boxed(lean_object* v_x_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_Lean_Meta_Sym_foldProjs___lam__1(v_x_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec_ref(v_x_2101_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs(lean_object* v_e_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_){
_start:
{
lean_object* v___f_2117_; lean_object* v___x_2118_; 
v___f_2117_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__0));
v___x_2118_ = lean_find_expr(v___f_2117_, v_e_2111_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v___x_2119_; 
v___x_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2119_, 0, v_e_2111_);
return v___x_2119_;
}
else
{
lean_object* v_post_2120_; lean_object* v___f_2121_; uint8_t v___x_2122_; lean_object* v___x_2123_; 
lean_dec_ref_known(v___x_2118_, 1);
v_post_2120_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__1));
v___f_2121_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__2));
v___x_2122_ = 0;
v___x_2123_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_e_2111_, v___f_2121_, v_post_2120_, v___x_2122_, v___x_2122_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
return v___x_2123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___boxed(lean_object* v_e_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Lean_Meta_Sym_foldProjs(v_e_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
lean_dec(v_a_2128_);
lean_dec_ref(v_a_2127_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
return v_res_2130_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2(void){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2134_ = lean_box(0);
v___x_2135_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1));
v___x_2136_ = l_Lean_mkConst(v___x_2135_, v___x_2134_);
return v___x_2136_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5(void){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2140_ = lean_box(0);
v___x_2141_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4));
v___x_2142_ = l_Lean_mkConst(v___x_2141_, v___x_2140_);
return v___x_2142_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9(void){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2148_ = lean_box(0);
v___x_2149_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8));
v___x_2150_ = l_Lean_mkConst(v___x_2149_, v___x_2148_);
return v___x_2150_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12(void){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2155_ = lean_box(0);
v___x_2156_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11));
v___x_2157_ = l_Lean_mkConst(v___x_2156_, v___x_2155_);
return v___x_2157_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13(void){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = lean_unsigned_to_nat(0u);
v___x_2159_ = l_Lean_mkNatLit(v___x_2158_);
return v___x_2159_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17(void){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2165_ = lean_box(0);
v___x_2166_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16));
v___x_2167_ = l_Lean_mkConst(v___x_2166_, v___x_2165_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(lean_object* v_a_2168_, lean_object* v_a_2169_){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2);
v___x_2171_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2170_, v_a_2168_, v_a_2169_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v_a_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2172_);
v_a_2173_ = lean_ctor_get(v___x_2171_, 1);
lean_inc(v_a_2173_);
lean_dec_ref_known(v___x_2171_, 2);
v___x_2174_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5);
v___x_2175_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2174_, v_a_2168_, v_a_2173_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v_a_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
v_a_2177_ = lean_ctor_get(v___x_2175_, 1);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2175_, 2);
v___x_2178_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9);
v___x_2179_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2178_, v_a_2168_, v_a_2177_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v_a_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
v_a_2181_ = lean_ctor_get(v___x_2179_, 1);
lean_inc(v_a_2181_);
lean_dec_ref_known(v___x_2179_, 2);
v___x_2182_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12);
v___x_2183_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2182_, v_a_2168_, v_a_2181_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v_a_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2184_);
v_a_2185_ = lean_ctor_get(v___x_2183_, 1);
lean_inc(v_a_2185_);
lean_dec_ref_known(v___x_2183_, 2);
v___x_2186_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13);
v___x_2187_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2186_, v_a_2168_, v_a_2185_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; lean_object* v_a_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_a_2188_);
v_a_2189_ = lean_ctor_get(v___x_2187_, 1);
lean_inc(v_a_2189_);
lean_dec_ref_known(v___x_2187_, 2);
v___x_2190_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17);
v___x_2191_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2190_, v_a_2168_, v_a_2189_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v_a_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_a_2192_);
v_a_2193_ = lean_ctor_get(v___x_2191_, 1);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2191_, 2);
v___x_2194_ = l_Lean_Int_mkType;
v___x_2195_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2194_, v_a_2168_, v_a_2193_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2205_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
v_a_2197_ = lean_ctor_get(v___x_2195_, 1);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2199_ = v___x_2195_;
v_isShared_2200_ = v_isSharedCheck_2205_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_inc(v_a_2196_);
lean_dec(v___x_2195_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2205_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2201_; lean_object* v___x_2203_; 
v___x_2201_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2201_, 0, v_a_2176_);
lean_ctor_set(v___x_2201_, 1, v_a_2172_);
lean_ctor_set(v___x_2201_, 2, v_a_2188_);
lean_ctor_set(v___x_2201_, 3, v_a_2184_);
lean_ctor_set(v___x_2201_, 4, v_a_2180_);
lean_ctor_set(v___x_2201_, 5, v_a_2192_);
lean_ctor_set(v___x_2201_, 6, v_a_2196_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v___x_2201_);
v___x_2203_ = v___x_2199_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2201_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_a_2197_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
else
{
lean_object* v_a_2206_; lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec(v_a_2192_);
lean_dec(v_a_2188_);
lean_dec(v_a_2184_);
lean_dec(v_a_2180_);
lean_dec(v_a_2176_);
lean_dec(v_a_2172_);
v_a_2206_ = lean_ctor_get(v___x_2195_, 0);
v_a_2207_ = lean_ctor_get(v___x_2195_, 1);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2195_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_inc(v_a_2206_);
lean_dec(v___x_2195_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2206_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
else
{
lean_object* v_a_2215_; lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec(v_a_2188_);
lean_dec(v_a_2184_);
lean_dec(v_a_2180_);
lean_dec(v_a_2176_);
lean_dec(v_a_2172_);
v_a_2215_ = lean_ctor_get(v___x_2191_, 0);
v_a_2216_ = lean_ctor_get(v___x_2191_, 1);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2191_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_inc(v_a_2215_);
lean_dec(v___x_2191_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2215_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
else
{
lean_object* v_a_2224_; lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec(v_a_2184_);
lean_dec(v_a_2180_);
lean_dec(v_a_2176_);
lean_dec(v_a_2172_);
v_a_2224_ = lean_ctor_get(v___x_2187_, 0);
v_a_2225_ = lean_ctor_get(v___x_2187_, 1);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2187_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_inc(v_a_2224_);
lean_dec(v___x_2187_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2224_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
else
{
lean_object* v_a_2233_; lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
lean_dec(v_a_2180_);
lean_dec(v_a_2176_);
lean_dec(v_a_2172_);
v_a_2233_ = lean_ctor_get(v___x_2183_, 0);
v_a_2234_ = lean_ctor_get(v___x_2183_, 1);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2183_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_inc(v_a_2233_);
lean_dec(v___x_2183_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2233_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
else
{
lean_object* v_a_2242_; lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
lean_dec(v_a_2176_);
lean_dec(v_a_2172_);
v_a_2242_ = lean_ctor_get(v___x_2179_, 0);
v_a_2243_ = lean_ctor_get(v___x_2179_, 1);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2179_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_inc(v_a_2242_);
lean_dec(v___x_2179_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2242_);
lean_ctor_set(v_reuseFailAlloc_2249_, 1, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
else
{
lean_object* v_a_2251_; lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2259_; 
lean_dec(v_a_2172_);
v_a_2251_ = lean_ctor_get(v___x_2175_, 0);
v_a_2252_ = lean_ctor_get(v___x_2175_, 1);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2254_ = v___x_2175_;
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_inc(v_a_2251_);
lean_dec(v___x_2175_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2257_; 
if (v_isShared_2255_ == 0)
{
v___x_2257_ = v___x_2254_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2251_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_a_2252_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
else
{
lean_object* v_a_2260_; lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
v_a_2260_ = lean_ctor_get(v___x_2171_, 0);
v_a_2261_ = lean_ctor_get(v___x_2171_, 1);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___x_2171_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_inc(v_a_2260_);
lean_dec(v___x_2171_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2260_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___boxed(lean_object* v_a_2269_, lean_object* v_a_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(v_a_2269_, v_a_2270_);
lean_dec_ref(v_a_2269_);
return v_res_2271_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(lean_object* v_opts_2272_, lean_object* v_opt_2273_){
_start:
{
lean_object* v_name_2274_; lean_object* v_defValue_2275_; lean_object* v_map_2276_; lean_object* v___x_2277_; 
v_name_2274_ = lean_ctor_get(v_opt_2273_, 0);
v_defValue_2275_ = lean_ctor_get(v_opt_2273_, 1);
v_map_2276_ = lean_ctor_get(v_opts_2272_, 0);
v___x_2277_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2276_, v_name_2274_);
if (lean_obj_tag(v___x_2277_) == 0)
{
uint8_t v___x_2278_; 
v___x_2278_ = lean_unbox(v_defValue_2275_);
return v___x_2278_;
}
else
{
lean_object* v_val_2279_; 
v_val_2279_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_val_2279_);
lean_dec_ref_known(v___x_2277_, 1);
if (lean_obj_tag(v_val_2279_) == 1)
{
uint8_t v_v_2280_; 
v_v_2280_ = lean_ctor_get_uint8(v_val_2279_, 0);
lean_dec_ref_known(v_val_2279_, 0);
return v_v_2280_;
}
else
{
uint8_t v___x_2281_; 
lean_dec(v_val_2279_);
v___x_2281_ = lean_unbox(v_defValue_2275_);
return v___x_2281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0___boxed(lean_object* v_opts_2282_, lean_object* v_opt_2283_){
_start:
{
uint8_t v_res_2284_; lean_object* v_r_2285_; 
v_res_2284_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(v_opts_2282_, v_opt_2283_);
lean_dec_ref(v_opt_2283_);
lean_dec_ref(v_opts_2282_);
v_r_2285_ = lean_box(v_res_2284_);
return v_r_2285_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2286_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2287_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0);
v___x_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1(lean_object* v_00_u03b2_2289_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__1);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(lean_object* v_msg_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v___f_2298_; lean_object* v___x_2090__overap_2299_; lean_object* v___x_2300_; 
v___f_2298_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___closed__0));
v___x_2090__overap_2299_ = lean_panic_fn_borrowed(v___f_2298_, v_msg_2292_);
lean_inc(v___y_2296_);
lean_inc_ref(v___y_2295_);
lean_inc(v___y_2294_);
lean_inc_ref(v___y_2293_);
v___x_2300_ = lean_apply_5(v___x_2090__overap_2299_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, lean_box(0));
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___boxed(lean_object* v_msg_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(v_msg_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
return v_res_2307_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2308_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__0, &l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0);
v___x_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
return v___x_2310_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_2312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
return v___x_2312_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1(lean_box(0));
return v___x_2313_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__7(void){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2317_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__6));
v___x_2318_ = lean_unsigned_to_nat(19u);
v___x_2319_ = lean_unsigned_to_nat(294u);
v___x_2320_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__5));
v___x_2321_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__4));
v___x_2322_ = l_mkPanicMessageWithDecl(v___x_2321_, v___x_2320_, v___x_2319_, v___x_2318_, v___x_2317_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object* v_x_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_){
_start:
{
lean_object* v_fst_2330_; lean_object* v_snd_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___x_2371_; lean_object* v_env_2372_; uint8_t v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2371_ = lean_st_ref_get(v_a_2327_);
v_env_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc_ref(v_env_2372_);
lean_dec(v___x_2371_);
v___x_2373_ = 0;
v___x_2374_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2374_, 0, v_env_2372_);
lean_ctor_set_uint8(v___x_2374_, sizeof(void*)*1, v___x_2373_);
lean_ctor_set_uint8(v___x_2374_, sizeof(void*)*1 + 1, v___x_2373_);
v___x_2375_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__3, &l_Lean_Meta_Sym_SymM_run___redArg___closed__3_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__3);
v___x_2376_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(v___x_2374_, v___x_2375_);
lean_dec_ref_known(v___x_2374_, 1);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v_a_2378_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_a_2377_);
v_a_2378_ = lean_ctor_get(v___x_2376_, 1);
lean_inc(v_a_2378_);
lean_dec_ref_known(v___x_2376_, 2);
v_fst_2330_ = v_a_2377_;
v_snd_2331_ = v_a_2378_;
v___y_2332_ = v_a_2324_;
v___y_2333_ = v_a_2325_;
v___y_2334_ = v_a_2326_;
v___y_2335_ = v_a_2327_;
goto v___jp_2329_;
}
else
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
lean_dec_ref_known(v___x_2376_, 2);
v___x_2379_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__7, &l_Lean_Meta_Sym_SymM_run___redArg___closed__7_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__7);
v___x_2380_ = l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(v___x_2379_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; lean_object* v_fst_2382_; lean_object* v_snd_2383_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2381_);
lean_dec_ref_known(v___x_2380_, 1);
v_fst_2382_ = lean_ctor_get(v_a_2381_, 0);
lean_inc(v_fst_2382_);
v_snd_2383_ = lean_ctor_get(v_a_2381_, 1);
lean_inc(v_snd_2383_);
lean_dec(v_a_2381_);
v_fst_2330_ = v_fst_2382_;
v_snd_2331_ = v_snd_2383_;
v___y_2332_ = v_a_2324_;
v___y_2333_ = v_a_2325_;
v___y_2334_ = v_a_2326_;
v___y_2335_ = v_a_2327_;
goto v___jp_2329_;
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
lean_dec_ref(v_x_2323_);
v_a_2384_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2380_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2380_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
v___jp_2329_:
{
lean_object* v___x_2336_; 
v___x_2336_ = l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v_options_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2336_, 1);
v_options_2338_ = lean_ctor_get(v___y_2334_, 2);
v___x_2339_ = l_Lean_Meta_Sym_sym_debug;
v___x_2340_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(v_options_2338_, v___x_2339_);
v___x_2341_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedConfig_default___closed__0));
v___x_2342_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__1, &l_Lean_Meta_Sym_SymM_run___redArg___closed__1_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1);
v___x_2343_ = lean_box(0);
v___x_2344_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__2, &l_Lean_Meta_Sym_SymM_run___redArg___closed__2_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__2);
v___x_2345_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_2345_, 0, v_snd_2331_);
lean_ctor_set(v___x_2345_, 1, v___x_2342_);
lean_ctor_set(v___x_2345_, 2, v___x_2342_);
lean_ctor_set(v___x_2345_, 3, v___x_2342_);
lean_ctor_set(v___x_2345_, 4, v___x_2342_);
lean_ctor_set(v___x_2345_, 5, v___x_2342_);
lean_ctor_set(v___x_2345_, 6, v___x_2342_);
lean_ctor_set(v___x_2345_, 7, v_a_2337_);
lean_ctor_set(v___x_2345_, 8, v___x_2343_);
lean_ctor_set(v___x_2345_, 9, v___x_2344_);
lean_ctor_set_uint8(v___x_2345_, sizeof(void*)*10, v___x_2340_);
v___x_2346_ = lean_st_mk_ref(v___x_2345_);
v___x_2347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2347_, 0, v_fst_2330_);
lean_ctor_set(v___x_2347_, 1, v___x_2341_);
lean_inc(v___y_2335_);
lean_inc_ref(v___y_2334_);
lean_inc(v___y_2333_);
lean_inc_ref(v___y_2332_);
lean_inc(v___x_2346_);
v___x_2348_ = lean_apply_7(v_x_2323_, v___x_2347_, v___x_2346_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, lean_box(0));
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2357_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2357_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2357_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; lean_object* v___x_2355_; 
v___x_2353_ = lean_st_ref_get(v___x_2346_);
lean_dec(v___x_2346_);
lean_dec(v___x_2353_);
if (v_isShared_2352_ == 0)
{
v___x_2355_ = v___x_2351_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2349_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
else
{
lean_dec(v___x_2346_);
return v___x_2348_;
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2370_; 
lean_dec_ref(v_snd_2331_);
lean_dec_ref(v_fst_2330_);
lean_dec_ref(v_x_2323_);
v_a_2358_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2360_ = v___x_2336_;
v_isShared_2361_ = v_isSharedCheck_2370_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2336_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2370_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v_ref_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2368_; 
v_ref_2362_ = lean_ctor_get(v___y_2334_, 5);
v___x_2363_ = lean_io_error_to_string(v_a_2358_);
v___x_2364_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
v___x_2365_ = l_Lean_MessageData_ofFormat(v___x_2364_);
lean_inc(v_ref_2362_);
v___x_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2366_, 0, v_ref_2362_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 0, v___x_2366_);
v___x_2368_ = v___x_2360_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2366_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg___boxed(lean_object* v_x_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
lean_dec(v_a_2396_);
lean_dec_ref(v_a_2395_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run(lean_object* v_00_u03b1_2399_, lean_object* v_x_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___boxed(lean_object* v_00_u03b1_2407_, lean_object* v_x_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Lean_Meta_Sym_SymM_run(v_00_u03b1_2407_, v_x_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_);
lean_dec(v_a_2412_);
lean_dec_ref(v_a_2411_);
lean_dec(v_a_2410_);
lean_dec_ref(v_a_2409_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg(lean_object* v_a_2415_){
_start:
{
lean_object* v_sharedExprs_2417_; lean_object* v___x_2418_; 
v_sharedExprs_2417_ = lean_ctor_get(v_a_2415_, 0);
lean_inc_ref(v_sharedExprs_2417_);
v___x_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2418_, 0, v_sharedExprs_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg___boxed(lean_object* v_a_2419_, lean_object* v_a_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2419_);
lean_dec_ref(v_a_2419_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs(lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2422_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___boxed(lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_Meta_Sym_getSharedExprs(v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object* v_a_2438_){
_start:
{
lean_object* v___x_2440_; lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2449_; 
v___x_2440_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2438_);
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2443_ = v___x_2440_;
v_isShared_2444_ = v_isSharedCheck_2449_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2440_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2449_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v_trueExpr_2445_; lean_object* v___x_2447_; 
v_trueExpr_2445_ = lean_ctor_get(v_a_2441_, 0);
lean_inc_ref(v_trueExpr_2445_);
lean_dec(v_a_2441_);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 0, v_trueExpr_2445_);
v___x_2447_ = v___x_2443_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_trueExpr_2445_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg___boxed(lean_object* v_a_2450_, lean_object* v_a_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2450_);
lean_dec_ref(v_a_2450_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr(lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v___x_2460_; 
v___x_2460_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2453_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___boxed(lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Lean_Meta_Sym_getTrueExpr(v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_);
lean_dec(v_a_2466_);
lean_dec_ref(v_a_2465_);
lean_dec(v_a_2464_);
lean_dec_ref(v_a_2463_);
lean_dec(v_a_2462_);
lean_dec_ref(v_a_2461_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object* v_e_2469_, lean_object* v_a_2470_){
_start:
{
lean_object* v___x_2472_; 
v___x_2472_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2470_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2482_; 
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2475_ = v___x_2472_;
v_isShared_2476_ = v_isSharedCheck_2482_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2472_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2482_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
uint8_t v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2480_; 
v___x_2477_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_2469_, v_a_2473_);
lean_dec(v_a_2473_);
v___x_2478_ = lean_box(v___x_2477_);
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 0, v___x_2478_);
v___x_2480_ = v___x_2475_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v___x_2478_);
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
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
v_a_2483_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2472_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2472_);
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
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg___boxed(lean_object* v_e_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_2491_, v_a_2492_);
lean_dec_ref(v_a_2492_);
lean_dec_ref(v_e_2491_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr(lean_object* v_e_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_){
_start:
{
lean_object* v___x_2503_; 
v___x_2503_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_2495_, v_a_2496_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___boxed(lean_object* v_e_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Lean_Meta_Sym_isTrueExpr(v_e_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_);
lean_dec(v_a_2510_);
lean_dec_ref(v_a_2509_);
lean_dec(v_a_2508_);
lean_dec_ref(v_a_2507_);
lean_dec(v_a_2506_);
lean_dec_ref(v_a_2505_);
lean_dec_ref(v_e_2504_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object* v_a_2513_){
_start:
{
lean_object* v___x_2515_; lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2524_; 
v___x_2515_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2513_);
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2524_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2524_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v_falseExpr_2520_; lean_object* v___x_2522_; 
v_falseExpr_2520_ = lean_ctor_get(v_a_2516_, 1);
lean_inc_ref(v_falseExpr_2520_);
lean_dec(v_a_2516_);
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v_falseExpr_2520_);
v___x_2522_ = v___x_2518_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_falseExpr_2520_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg___boxed(lean_object* v_a_2525_, lean_object* v_a_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2525_);
lean_dec_ref(v_a_2525_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr(lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2528_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___boxed(lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l_Lean_Meta_Sym_getFalseExpr(v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_);
lean_dec(v_a_2541_);
lean_dec_ref(v_a_2540_);
lean_dec(v_a_2539_);
lean_dec_ref(v_a_2538_);
lean_dec(v_a_2537_);
lean_dec_ref(v_a_2536_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object* v_e_2544_, lean_object* v_a_2545_){
_start:
{
lean_object* v___x_2547_; 
v___x_2547_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2545_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2557_; 
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2550_ = v___x_2547_;
v_isShared_2551_ = v_isSharedCheck_2557_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2547_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2557_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
uint8_t v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2555_; 
v___x_2552_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_2544_, v_a_2548_);
lean_dec(v_a_2548_);
v___x_2553_ = lean_box(v___x_2552_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 0, v___x_2553_);
v___x_2555_ = v___x_2550_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2553_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
v_a_2558_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2560_ = v___x_2547_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2547_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2558_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg___boxed(lean_object* v_e_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_2566_, v_a_2567_);
lean_dec_ref(v_a_2567_);
lean_dec_ref(v_e_2566_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr(lean_object* v_e_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_){
_start:
{
lean_object* v___x_2578_; 
v___x_2578_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_2570_, v_a_2571_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___boxed(lean_object* v_e_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Lean_Meta_Sym_isFalseExpr(v_e_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_);
lean_dec(v_a_2585_);
lean_dec_ref(v_a_2584_);
lean_dec(v_a_2583_);
lean_dec_ref(v_a_2582_);
lean_dec(v_a_2581_);
lean_dec_ref(v_a_2580_);
lean_dec_ref(v_e_2579_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object* v_a_2588_){
_start:
{
lean_object* v___x_2590_; lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2599_; 
v___x_2590_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2588_);
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2593_ = v___x_2590_;
v_isShared_2594_ = v_isSharedCheck_2599_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2590_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2599_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v_btrueExpr_2595_; lean_object* v___x_2597_; 
v_btrueExpr_2595_ = lean_ctor_get(v_a_2591_, 3);
lean_inc_ref(v_btrueExpr_2595_);
lean_dec(v_a_2591_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v_btrueExpr_2595_);
v___x_2597_ = v___x_2593_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_btrueExpr_2595_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg___boxed(lean_object* v_a_2600_, lean_object* v_a_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2600_);
lean_dec_ref(v_a_2600_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr(lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_){
_start:
{
lean_object* v___x_2610_; 
v___x_2610_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2603_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___boxed(lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l_Lean_Meta_Sym_getBoolTrueExpr(v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_);
lean_dec(v_a_2616_);
lean_dec_ref(v_a_2615_);
lean_dec(v_a_2614_);
lean_dec_ref(v_a_2613_);
lean_dec(v_a_2612_);
lean_dec_ref(v_a_2611_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg(lean_object* v_e_2619_, lean_object* v_a_2620_){
_start:
{
lean_object* v___x_2622_; 
v___x_2622_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2620_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2632_; 
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2625_ = v___x_2622_;
v_isShared_2626_ = v_isSharedCheck_2632_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2622_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2632_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
uint8_t v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2630_; 
v___x_2627_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_2619_, v_a_2623_);
lean_dec(v_a_2623_);
v___x_2628_ = lean_box(v___x_2627_);
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 0, v___x_2628_);
v___x_2630_ = v___x_2625_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2628_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
v_a_2633_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2622_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2622_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg___boxed(lean_object* v_e_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_2641_, v_a_2642_);
lean_dec_ref(v_a_2642_);
lean_dec_ref(v_e_2641_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr(lean_object* v_e_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_){
_start:
{
lean_object* v___x_2653_; 
v___x_2653_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_2645_, v_a_2646_);
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___boxed(lean_object* v_e_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l_Lean_Meta_Sym_isBoolTrueExpr(v_e_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec_ref(v_a_2657_);
lean_dec(v_a_2656_);
lean_dec_ref(v_a_2655_);
lean_dec_ref(v_e_2654_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object* v_a_2663_){
_start:
{
lean_object* v___x_2665_; lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2674_; 
v___x_2665_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2663_);
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2668_ = v___x_2665_;
v_isShared_2669_ = v_isSharedCheck_2674_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2665_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2674_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v_bfalseExpr_2670_; lean_object* v___x_2672_; 
v_bfalseExpr_2670_ = lean_ctor_get(v_a_2666_, 4);
lean_inc_ref(v_bfalseExpr_2670_);
lean_dec(v_a_2666_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v_bfalseExpr_2670_);
v___x_2672_ = v___x_2668_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_bfalseExpr_2670_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg___boxed(lean_object* v_a_2675_, lean_object* v_a_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2675_);
lean_dec_ref(v_a_2675_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr(lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
lean_object* v___x_2685_; 
v___x_2685_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2678_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___boxed(lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Lean_Meta_Sym_getBoolFalseExpr(v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg(lean_object* v_e_2694_, lean_object* v_a_2695_){
_start:
{
lean_object* v___x_2697_; 
v___x_2697_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2695_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2707_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2700_ = v___x_2697_;
v_isShared_2701_ = v_isSharedCheck_2707_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2697_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2707_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
uint8_t v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2705_; 
v___x_2702_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_2694_, v_a_2698_);
lean_dec(v_a_2698_);
v___x_2703_ = lean_box(v___x_2702_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v___x_2703_);
v___x_2705_ = v___x_2700_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2703_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
else
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
v_a_2708_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v___x_2697_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2697_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg___boxed(lean_object* v_e_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_2716_, v_a_2717_);
lean_dec_ref(v_a_2717_);
lean_dec_ref(v_e_2716_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr(lean_object* v_e_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
lean_object* v___x_2728_; 
v___x_2728_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_2720_, v_a_2721_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___boxed(lean_object* v_e_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Lean_Meta_Sym_isBoolFalseExpr(v_e_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_);
lean_dec(v_a_2735_);
lean_dec_ref(v_a_2734_);
lean_dec(v_a_2733_);
lean_dec_ref(v_a_2732_);
lean_dec(v_a_2731_);
lean_dec_ref(v_a_2730_);
lean_dec_ref(v_e_2729_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg(lean_object* v_a_2738_){
_start:
{
lean_object* v___x_2740_; lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2749_; 
v___x_2740_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2738_);
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2743_ = v___x_2740_;
v_isShared_2744_ = v_isSharedCheck_2749_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2740_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2749_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v_natZExpr_2745_; lean_object* v___x_2747_; 
v_natZExpr_2745_ = lean_ctor_get(v_a_2741_, 2);
lean_inc_ref(v_natZExpr_2745_);
lean_dec(v_a_2741_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 0, v_natZExpr_2745_);
v___x_2747_ = v___x_2743_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_natZExpr_2745_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg___boxed(lean_object* v_a_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_2750_);
lean_dec_ref(v_a_2750_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr(lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_2753_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___boxed(lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Lean_Meta_Sym_getNatZeroExpr(v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_);
lean_dec(v_a_2766_);
lean_dec_ref(v_a_2765_);
lean_dec(v_a_2764_);
lean_dec_ref(v_a_2763_);
lean_dec(v_a_2762_);
lean_dec_ref(v_a_2761_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg(lean_object* v_a_2769_){
_start:
{
lean_object* v___x_2771_; lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2780_; 
v___x_2771_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2769_);
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2774_ = v___x_2771_;
v_isShared_2775_ = v_isSharedCheck_2780_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2780_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v_ordEqExpr_2776_; lean_object* v___x_2778_; 
v_ordEqExpr_2776_ = lean_ctor_get(v_a_2772_, 5);
lean_inc_ref(v_ordEqExpr_2776_);
lean_dec(v_a_2772_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v_ordEqExpr_2776_);
v___x_2778_ = v___x_2774_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_ordEqExpr_2776_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg___boxed(lean_object* v_a_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_2781_);
lean_dec_ref(v_a_2781_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr(lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_){
_start:
{
lean_object* v___x_2791_; 
v___x_2791_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_2784_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___boxed(lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Lean_Meta_Sym_getOrderingEqExpr(v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
lean_dec(v_a_2797_);
lean_dec_ref(v_a_2796_);
lean_dec(v_a_2795_);
lean_dec_ref(v_a_2794_);
lean_dec(v_a_2793_);
lean_dec_ref(v_a_2792_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg(lean_object* v_a_2800_){
_start:
{
lean_object* v___x_2802_; lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2811_; 
v___x_2802_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2800_);
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2805_ = v___x_2802_;
v_isShared_2806_ = v_isSharedCheck_2811_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2802_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2811_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v_intExpr_2807_; lean_object* v___x_2809_; 
v_intExpr_2807_ = lean_ctor_get(v_a_2803_, 6);
lean_inc_ref(v_intExpr_2807_);
lean_dec(v_a_2803_);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 0, v_intExpr_2807_);
v___x_2809_ = v___x_2805_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_intExpr_2807_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg___boxed(lean_object* v_a_2812_, lean_object* v_a_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_2812_);
lean_dec_ref(v_a_2812_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr(lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_){
_start:
{
lean_object* v___x_2822_; 
v___x_2822_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_2815_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___boxed(lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_Lean_Meta_Sym_getIntExpr(v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_);
lean_dec(v_a_2828_);
lean_dec_ref(v_a_2827_);
lean_dec(v_a_2826_);
lean_dec_ref(v_a_2825_);
lean_dec(v_a_2824_);
lean_dec_ref(v_a_2823_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg(lean_object* v_k_2831_, lean_object* v_ctx_2832_, lean_object* v_a_2833_){
_start:
{
lean_object* v___x_2835_; lean_object* v_share_2836_; lean_object* v_maxFVar_2837_; lean_object* v_proofInstInfo_2838_; lean_object* v_inferType_2839_; lean_object* v_getLevel_2840_; lean_object* v_congrInfo_2841_; lean_object* v_defEqI_2842_; lean_object* v_extensions_2843_; lean_object* v_issues_2844_; lean_object* v_canon_2845_; uint8_t v_debug_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2904_; 
v___x_2835_ = lean_st_ref_take(v_a_2833_);
v_share_2836_ = lean_ctor_get(v___x_2835_, 0);
v_maxFVar_2837_ = lean_ctor_get(v___x_2835_, 1);
v_proofInstInfo_2838_ = lean_ctor_get(v___x_2835_, 2);
v_inferType_2839_ = lean_ctor_get(v___x_2835_, 3);
v_getLevel_2840_ = lean_ctor_get(v___x_2835_, 4);
v_congrInfo_2841_ = lean_ctor_get(v___x_2835_, 5);
v_defEqI_2842_ = lean_ctor_get(v___x_2835_, 6);
v_extensions_2843_ = lean_ctor_get(v___x_2835_, 7);
v_issues_2844_ = lean_ctor_get(v___x_2835_, 8);
v_canon_2845_ = lean_ctor_get(v___x_2835_, 9);
v_debug_2846_ = lean_ctor_get_uint8(v___x_2835_, sizeof(void*)*10);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2848_ = v___x_2835_;
v_isShared_2849_ = v_isSharedCheck_2904_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_canon_2845_);
lean_inc(v_issues_2844_);
lean_inc(v_extensions_2843_);
lean_inc(v_defEqI_2842_);
lean_inc(v_congrInfo_2841_);
lean_inc(v_getLevel_2840_);
lean_inc(v_inferType_2839_);
lean_inc(v_proofInstInfo_2838_);
lean_inc(v_maxFVar_2837_);
lean_inc(v_share_2836_);
lean_dec(v___x_2835_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2904_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2850_; lean_object* v___x_2852_; 
v___x_2850_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__3, &l_Lean_Meta_Sym_SymM_run___redArg___closed__3_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__3);
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 0, v___x_2850_);
v___x_2852_ = v___x_2848_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2850_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_maxFVar_2837_);
lean_ctor_set(v_reuseFailAlloc_2903_, 2, v_proofInstInfo_2838_);
lean_ctor_set(v_reuseFailAlloc_2903_, 3, v_inferType_2839_);
lean_ctor_set(v_reuseFailAlloc_2903_, 4, v_getLevel_2840_);
lean_ctor_set(v_reuseFailAlloc_2903_, 5, v_congrInfo_2841_);
lean_ctor_set(v_reuseFailAlloc_2903_, 6, v_defEqI_2842_);
lean_ctor_set(v_reuseFailAlloc_2903_, 7, v_extensions_2843_);
lean_ctor_set(v_reuseFailAlloc_2903_, 8, v_issues_2844_);
lean_ctor_set(v_reuseFailAlloc_2903_, 9, v_canon_2845_);
lean_ctor_set_uint8(v_reuseFailAlloc_2903_, sizeof(void*)*10, v_debug_2846_);
v___x_2852_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = lean_st_ref_set(v_a_2833_, v___x_2852_);
v___x_2854_ = lean_apply_2(v_k_2831_, v_ctx_2832_, v_share_2836_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v_a_2856_; lean_object* v___x_2857_; lean_object* v_maxFVar_2858_; lean_object* v_proofInstInfo_2859_; lean_object* v_inferType_2860_; lean_object* v_getLevel_2861_; lean_object* v_congrInfo_2862_; lean_object* v_defEqI_2863_; lean_object* v_extensions_2864_; lean_object* v_issues_2865_; lean_object* v_canon_2866_; uint8_t v_debug_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2877_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
v_a_2856_ = lean_ctor_get(v___x_2854_, 1);
lean_inc(v_a_2856_);
lean_dec_ref_known(v___x_2854_, 2);
v___x_2857_ = lean_st_ref_take(v_a_2833_);
v_maxFVar_2858_ = lean_ctor_get(v___x_2857_, 1);
v_proofInstInfo_2859_ = lean_ctor_get(v___x_2857_, 2);
v_inferType_2860_ = lean_ctor_get(v___x_2857_, 3);
v_getLevel_2861_ = lean_ctor_get(v___x_2857_, 4);
v_congrInfo_2862_ = lean_ctor_get(v___x_2857_, 5);
v_defEqI_2863_ = lean_ctor_get(v___x_2857_, 6);
v_extensions_2864_ = lean_ctor_get(v___x_2857_, 7);
v_issues_2865_ = lean_ctor_get(v___x_2857_, 8);
v_canon_2866_ = lean_ctor_get(v___x_2857_, 9);
v_debug_2867_ = lean_ctor_get_uint8(v___x_2857_, sizeof(void*)*10);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2877_ == 0)
{
lean_object* v_unused_2878_; 
v_unused_2878_ = lean_ctor_get(v___x_2857_, 0);
lean_dec(v_unused_2878_);
v___x_2869_ = v___x_2857_;
v_isShared_2870_ = v_isSharedCheck_2877_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_canon_2866_);
lean_inc(v_issues_2865_);
lean_inc(v_extensions_2864_);
lean_inc(v_defEqI_2863_);
lean_inc(v_congrInfo_2862_);
lean_inc(v_getLevel_2861_);
lean_inc(v_inferType_2860_);
lean_inc(v_proofInstInfo_2859_);
lean_inc(v_maxFVar_2858_);
lean_dec(v___x_2857_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2877_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 0, v_a_2856_);
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2856_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_maxFVar_2858_);
lean_ctor_set(v_reuseFailAlloc_2876_, 2, v_proofInstInfo_2859_);
lean_ctor_set(v_reuseFailAlloc_2876_, 3, v_inferType_2860_);
lean_ctor_set(v_reuseFailAlloc_2876_, 4, v_getLevel_2861_);
lean_ctor_set(v_reuseFailAlloc_2876_, 5, v_congrInfo_2862_);
lean_ctor_set(v_reuseFailAlloc_2876_, 6, v_defEqI_2863_);
lean_ctor_set(v_reuseFailAlloc_2876_, 7, v_extensions_2864_);
lean_ctor_set(v_reuseFailAlloc_2876_, 8, v_issues_2865_);
lean_ctor_set(v_reuseFailAlloc_2876_, 9, v_canon_2866_);
lean_ctor_set_uint8(v_reuseFailAlloc_2876_, sizeof(void*)*10, v_debug_2867_);
v___x_2872_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2873_ = lean_st_ref_set(v_a_2833_, v___x_2872_);
v___x_2874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2874_, 0, v_a_2855_);
v___x_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2874_);
return v___x_2875_;
}
}
}
else
{
lean_object* v_a_2879_; lean_object* v_a_2880_; lean_object* v___x_2881_; lean_object* v_maxFVar_2882_; lean_object* v_proofInstInfo_2883_; lean_object* v_inferType_2884_; lean_object* v_getLevel_2885_; lean_object* v_congrInfo_2886_; lean_object* v_defEqI_2887_; lean_object* v_extensions_2888_; lean_object* v_issues_2889_; lean_object* v_canon_2890_; uint8_t v_debug_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2901_; 
v_a_2879_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2879_);
v_a_2880_ = lean_ctor_get(v___x_2854_, 1);
lean_inc(v_a_2880_);
lean_dec_ref_known(v___x_2854_, 2);
v___x_2881_ = lean_st_ref_take(v_a_2833_);
v_maxFVar_2882_ = lean_ctor_get(v___x_2881_, 1);
v_proofInstInfo_2883_ = lean_ctor_get(v___x_2881_, 2);
v_inferType_2884_ = lean_ctor_get(v___x_2881_, 3);
v_getLevel_2885_ = lean_ctor_get(v___x_2881_, 4);
v_congrInfo_2886_ = lean_ctor_get(v___x_2881_, 5);
v_defEqI_2887_ = lean_ctor_get(v___x_2881_, 6);
v_extensions_2888_ = lean_ctor_get(v___x_2881_, 7);
v_issues_2889_ = lean_ctor_get(v___x_2881_, 8);
v_canon_2890_ = lean_ctor_get(v___x_2881_, 9);
v_debug_2891_ = lean_ctor_get_uint8(v___x_2881_, sizeof(void*)*10);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2901_ == 0)
{
lean_object* v_unused_2902_; 
v_unused_2902_ = lean_ctor_get(v___x_2881_, 0);
lean_dec(v_unused_2902_);
v___x_2893_ = v___x_2881_;
v_isShared_2894_ = v_isSharedCheck_2901_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_canon_2890_);
lean_inc(v_issues_2889_);
lean_inc(v_extensions_2888_);
lean_inc(v_defEqI_2887_);
lean_inc(v_congrInfo_2886_);
lean_inc(v_getLevel_2885_);
lean_inc(v_inferType_2884_);
lean_inc(v_proofInstInfo_2883_);
lean_inc(v_maxFVar_2882_);
lean_dec(v___x_2881_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2901_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 0, v_a_2880_);
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2880_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v_maxFVar_2882_);
lean_ctor_set(v_reuseFailAlloc_2900_, 2, v_proofInstInfo_2883_);
lean_ctor_set(v_reuseFailAlloc_2900_, 3, v_inferType_2884_);
lean_ctor_set(v_reuseFailAlloc_2900_, 4, v_getLevel_2885_);
lean_ctor_set(v_reuseFailAlloc_2900_, 5, v_congrInfo_2886_);
lean_ctor_set(v_reuseFailAlloc_2900_, 6, v_defEqI_2887_);
lean_ctor_set(v_reuseFailAlloc_2900_, 7, v_extensions_2888_);
lean_ctor_set(v_reuseFailAlloc_2900_, 8, v_issues_2889_);
lean_ctor_set(v_reuseFailAlloc_2900_, 9, v_canon_2890_);
lean_ctor_set_uint8(v_reuseFailAlloc_2900_, sizeof(void*)*10, v_debug_2891_);
v___x_2896_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2897_ = lean_st_ref_set(v_a_2833_, v___x_2896_);
v___x_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2898_, 0, v_a_2879_);
v___x_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
return v___x_2899_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg___boxed(lean_object* v_k_2905_, lean_object* v_ctx_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v_k_2905_, v_ctx_2906_, v_a_2907_);
lean_dec(v_a_2907_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM(lean_object* v_00_u03b1_2910_, lean_object* v_k_2911_, lean_object* v_ctx_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_){
_start:
{
lean_object* v___x_2920_; 
v___x_2920_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v_k_2911_, v_ctx_2912_, v_a_2914_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___boxed(lean_object* v_00_u03b1_2921_, lean_object* v_k_2922_, lean_object* v_ctx_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Lean_Meta_Sym_runShareCommonM(v_00_u03b1_2921_, v_k_2922_, v_ctx_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_);
lean_dec(v_a_2929_);
lean_dec_ref(v_a_2928_);
lean_dec(v_a_2927_);
lean_dec_ref(v_a_2926_);
lean_dec(v_a_2925_);
lean_dec_ref(v_a_2924_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___lam__0(lean_object* v_ctx_2932_){
_start:
{
lean_object* v_config_2933_; lean_object* v_sharedExprs_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2951_; 
v_config_2933_ = lean_ctor_get(v_ctx_2932_, 1);
v_sharedExprs_2934_ = lean_ctor_get(v_ctx_2932_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v_ctx_2932_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2936_ = v_ctx_2932_;
v_isShared_2937_ = v_isSharedCheck_2951_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_config_2933_);
lean_inc(v_sharedExprs_2934_);
lean_dec(v_ctx_2932_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2951_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
uint8_t v_verbose_2938_; uint8_t v_enforceUnfoldReducible_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2950_; 
v_verbose_2938_ = lean_ctor_get_uint8(v_config_2933_, 0);
v_enforceUnfoldReducible_2939_ = lean_ctor_get_uint8(v_config_2933_, 1);
v_isSharedCheck_2950_ = !lean_is_exclusive(v_config_2933_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2941_ = v_config_2933_;
v_isShared_2942_ = v_isSharedCheck_2950_;
goto v_resetjp_2940_;
}
else
{
lean_dec(v_config_2933_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2950_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
uint8_t v___x_2943_; lean_object* v___x_2945_; 
v___x_2943_ = 0;
if (v_isShared_2942_ == 0)
{
v___x_2945_ = v___x_2941_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_2949_, 0, v_verbose_2938_);
lean_ctor_set_uint8(v_reuseFailAlloc_2949_, 1, v_enforceUnfoldReducible_2939_);
v___x_2945_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
lean_object* v___x_2947_; 
lean_ctor_set_uint8(v___x_2945_, 2, v___x_2943_);
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 1, v___x_2945_);
v___x_2947_ = v___x_2936_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_sharedExprs_2934_);
lean_ctor_set(v_reuseFailAlloc_2948_, 1, v___x_2945_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg(lean_object* v_inst_2953_, lean_object* v_x_2954_){
_start:
{
lean_object* v___f_2955_; lean_object* v___x_2956_; 
v___f_2955_ = ((lean_object*)(l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___closed__0));
v___x_2956_ = lean_apply_3(v_inst_2953_, lean_box(0), v___f_2955_, v_x_2954_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck(lean_object* v_m_2957_, lean_object* v_00_u03b1_2958_, lean_object* v_inst_2959_, lean_object* v_x_2960_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg(v_inst_2959_, v_x_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___lam__0(lean_object* v_ctx_2962_){
_start:
{
lean_object* v_config_2963_; lean_object* v_sharedExprs_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2980_; 
v_config_2963_ = lean_ctor_get(v_ctx_2962_, 1);
v_sharedExprs_2964_ = lean_ctor_get(v_ctx_2962_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v_ctx_2962_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2966_ = v_ctx_2962_;
v_isShared_2967_ = v_isSharedCheck_2980_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_config_2963_);
lean_inc(v_sharedExprs_2964_);
lean_dec(v_ctx_2962_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2980_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
uint8_t v_verbose_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2979_; 
v_verbose_2968_ = lean_ctor_get_uint8(v_config_2963_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v_config_2963_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2970_ = v_config_2963_;
v_isShared_2971_ = v_isSharedCheck_2979_;
goto v_resetjp_2969_;
}
else
{
lean_dec(v_config_2963_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2979_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
uint8_t v___x_2972_; lean_object* v___x_2974_; 
v___x_2972_ = 0;
if (v_isShared_2971_ == 0)
{
v___x_2974_ = v___x_2970_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_2978_, 0, v_verbose_2968_);
v___x_2974_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
lean_object* v___x_2976_; 
lean_ctor_set_uint8(v___x_2974_, 1, v___x_2972_);
lean_ctor_set_uint8(v___x_2974_, 2, v___x_2972_);
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 1, v___x_2974_);
v___x_2976_ = v___x_2966_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_sharedExprs_2964_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v___x_2974_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg(lean_object* v_inst_2982_, lean_object* v_x_2983_){
_start:
{
lean_object* v___f_2984_; lean_object* v___x_2985_; 
v___f_2984_ = ((lean_object*)(l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___closed__0));
v___x_2985_ = lean_apply_3(v_inst_2982_, lean_box(0), v___f_2984_, v_x_2983_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks(lean_object* v_m_2986_, lean_object* v_00_u03b1_2987_, lean_object* v_inst_2988_, lean_object* v_x_2989_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Lean_Meta_Sym_withoutShareCommonChecks___redArg(v_inst_2988_, v_x_2989_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(lean_object* v_a_2991_, lean_object* v_a_2992_){
_start:
{
lean_object* v___x_2994_; lean_object* v_config_2995_; lean_object* v_env_2996_; uint8_t v_enforceUnfoldReducible_2997_; uint8_t v_enforceFoldProjs_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2994_ = lean_st_ref_get(v_a_2992_);
v_config_2995_ = lean_ctor_get(v_a_2991_, 1);
v_env_2996_ = lean_ctor_get(v___x_2994_, 0);
lean_inc_ref(v_env_2996_);
lean_dec(v___x_2994_);
v_enforceUnfoldReducible_2997_ = lean_ctor_get_uint8(v_config_2995_, 1);
v_enforceFoldProjs_2998_ = lean_ctor_get_uint8(v_config_2995_, 2);
v___x_2999_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2999_, 0, v_env_2996_);
lean_ctor_set_uint8(v___x_2999_, sizeof(void*)*1, v_enforceUnfoldReducible_2997_);
lean_ctor_set_uint8(v___x_2999_, sizeof(void*)*1 + 1, v_enforceFoldProjs_2998_);
v___x_3000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2999_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg___boxed(lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3001_, v_a_3002_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx(lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_){
_start:
{
lean_object* v___x_3012_; 
v___x_3012_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3005_, v_a_3010_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___boxed(lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx(v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
lean_dec(v_a_3018_);
lean_dec_ref(v_a_3017_);
lean_dec(v_a_3016_);
lean_dec_ref(v_a_3015_);
lean_dec(v_a_3014_);
lean_dec_ref(v_a_3013_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(lean_object* v_e_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_){
_start:
{
lean_object* v_config_3028_; uint8_t v_enforceUnfoldReducible_3029_; uint8_t v_enforceFoldProjs_3030_; lean_object* v_e_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v_e_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; 
v_config_3028_ = lean_ctor_get(v_a_3022_, 1);
v_enforceUnfoldReducible_3029_ = lean_ctor_get_uint8(v_config_3028_, 1);
v_enforceFoldProjs_3030_ = lean_ctor_get_uint8(v_config_3028_, 2);
if (v_enforceUnfoldReducible_3029_ == 0)
{
v_e_3040_ = v_e_3021_;
v___y_3041_ = v_a_3023_;
v___y_3042_ = v_a_3024_;
v___y_3043_ = v_a_3025_;
v___y_3044_ = v_a_3026_;
goto v___jp_3039_;
}
else
{
lean_object* v___x_3047_; 
v___x_3047_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3021_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref_known(v___x_3047_, 1);
v_e_3040_ = v_a_3048_;
v___y_3041_ = v_a_3023_;
v___y_3042_ = v_a_3024_;
v___y_3043_ = v_a_3025_;
v___y_3044_ = v_a_3026_;
goto v___jp_3039_;
}
else
{
return v___x_3047_;
}
}
v___jp_3031_:
{
if (v_enforceUnfoldReducible_3029_ == 0)
{
lean_object* v___x_3037_; 
v___x_3037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3037_, 0, v_e_3032_);
return v___x_3037_;
}
else
{
lean_object* v___x_3038_; 
v___x_3038_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
return v___x_3038_;
}
}
v___jp_3039_:
{
if (v_enforceFoldProjs_3030_ == 0)
{
v_e_3032_ = v_e_3040_;
v___y_3033_ = v___y_3041_;
v___y_3034_ = v___y_3042_;
v___y_3035_ = v___y_3043_;
v___y_3036_ = v___y_3044_;
goto v___jp_3031_;
}
else
{
lean_object* v___x_3045_; 
v___x_3045_ = l_Lean_Meta_Sym_foldProjs(v_e_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v_a_3046_; 
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
lean_inc(v_a_3046_);
lean_dec_ref_known(v___x_3045_, 1);
v_e_3032_ = v_a_3046_;
v___y_3033_ = v___y_3041_;
v___y_3034_ = v___y_3042_;
v___y_3035_ = v___y_3043_;
v___y_3036_ = v___y_3044_;
goto v___jp_3031_;
}
else
{
return v___x_3045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg___boxed(lean_object* v_e_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_);
lean_dec(v_a_3054_);
lean_dec_ref(v_a_3053_);
lean_dec(v_a_3052_);
lean_dec_ref(v_a_3051_);
lean_dec_ref(v_a_3050_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation(lean_object* v_e_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3057_, v_a_3058_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___boxed(lean_object* v_e_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation(v_e_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
return v_res_3074_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3075_; 
v___x_3075_ = l_instMonadEIO(lean_box(0));
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(lean_object* v_msg_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v_toApplicative_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3153_; 
v___x_3088_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0);
v___x_3089_ = l_StateRefT_x27_instMonad___redArg(v___x_3088_);
v_toApplicative_3090_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3153_ == 0)
{
lean_object* v_unused_3154_; 
v_unused_3154_ = lean_ctor_get(v___x_3089_, 1);
lean_dec(v_unused_3154_);
v___x_3092_ = v___x_3089_;
v_isShared_3093_ = v_isSharedCheck_3153_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_toApplicative_3090_);
lean_dec(v___x_3089_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3153_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v_toFunctor_3094_; lean_object* v_toSeq_3095_; lean_object* v_toSeqLeft_3096_; lean_object* v_toSeqRight_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3151_; 
v_toFunctor_3094_ = lean_ctor_get(v_toApplicative_3090_, 0);
v_toSeq_3095_ = lean_ctor_get(v_toApplicative_3090_, 2);
v_toSeqLeft_3096_ = lean_ctor_get(v_toApplicative_3090_, 3);
v_toSeqRight_3097_ = lean_ctor_get(v_toApplicative_3090_, 4);
v_isSharedCheck_3151_ = !lean_is_exclusive(v_toApplicative_3090_);
if (v_isSharedCheck_3151_ == 0)
{
lean_object* v_unused_3152_; 
v_unused_3152_ = lean_ctor_get(v_toApplicative_3090_, 1);
lean_dec(v_unused_3152_);
v___x_3099_ = v_toApplicative_3090_;
v_isShared_3100_ = v_isSharedCheck_3151_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_toSeqRight_3097_);
lean_inc(v_toSeqLeft_3096_);
lean_inc(v_toSeq_3095_);
lean_inc(v_toFunctor_3094_);
lean_dec(v_toApplicative_3090_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3151_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___f_3101_; lean_object* v___f_3102_; lean_object* v___f_3103_; lean_object* v___f_3104_; lean_object* v___x_3105_; lean_object* v___f_3106_; lean_object* v___f_3107_; lean_object* v___f_3108_; lean_object* v___x_3110_; 
v___f_3101_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1));
v___f_3102_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2));
lean_inc_ref(v_toFunctor_3094_);
v___f_3103_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3103_, 0, v_toFunctor_3094_);
v___f_3104_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3104_, 0, v_toFunctor_3094_);
v___x_3105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3105_, 0, v___f_3103_);
lean_ctor_set(v___x_3105_, 1, v___f_3104_);
v___f_3106_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3106_, 0, v_toSeqRight_3097_);
v___f_3107_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3107_, 0, v_toSeqLeft_3096_);
v___f_3108_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3108_, 0, v_toSeq_3095_);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 4, v___f_3106_);
lean_ctor_set(v___x_3099_, 3, v___f_3107_);
lean_ctor_set(v___x_3099_, 2, v___f_3108_);
lean_ctor_set(v___x_3099_, 1, v___f_3101_);
lean_ctor_set(v___x_3099_, 0, v___x_3105_);
v___x_3110_ = v___x_3099_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3105_);
lean_ctor_set(v_reuseFailAlloc_3150_, 1, v___f_3101_);
lean_ctor_set(v_reuseFailAlloc_3150_, 2, v___f_3108_);
lean_ctor_set(v_reuseFailAlloc_3150_, 3, v___f_3107_);
lean_ctor_set(v_reuseFailAlloc_3150_, 4, v___f_3106_);
v___x_3110_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
lean_object* v___x_3112_; 
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 1, v___f_3102_);
lean_ctor_set(v___x_3092_, 0, v___x_3110_);
v___x_3112_ = v___x_3092_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v___x_3110_);
lean_ctor_set(v_reuseFailAlloc_3149_, 1, v___f_3102_);
v___x_3112_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
lean_object* v___x_3113_; lean_object* v_toApplicative_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3147_; 
v___x_3113_ = l_StateRefT_x27_instMonad___redArg(v___x_3112_);
v_toApplicative_3114_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3147_ == 0)
{
lean_object* v_unused_3148_; 
v_unused_3148_ = lean_ctor_get(v___x_3113_, 1);
lean_dec(v_unused_3148_);
v___x_3116_ = v___x_3113_;
v_isShared_3117_ = v_isSharedCheck_3147_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_toApplicative_3114_);
lean_dec(v___x_3113_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3147_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v_toFunctor_3118_; lean_object* v_toSeq_3119_; lean_object* v_toSeqLeft_3120_; lean_object* v_toSeqRight_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3145_; 
v_toFunctor_3118_ = lean_ctor_get(v_toApplicative_3114_, 0);
v_toSeq_3119_ = lean_ctor_get(v_toApplicative_3114_, 2);
v_toSeqLeft_3120_ = lean_ctor_get(v_toApplicative_3114_, 3);
v_toSeqRight_3121_ = lean_ctor_get(v_toApplicative_3114_, 4);
v_isSharedCheck_3145_ = !lean_is_exclusive(v_toApplicative_3114_);
if (v_isSharedCheck_3145_ == 0)
{
lean_object* v_unused_3146_; 
v_unused_3146_ = lean_ctor_get(v_toApplicative_3114_, 1);
lean_dec(v_unused_3146_);
v___x_3123_ = v_toApplicative_3114_;
v_isShared_3124_ = v_isSharedCheck_3145_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_toSeqRight_3121_);
lean_inc(v_toSeqLeft_3120_);
lean_inc(v_toSeq_3119_);
lean_inc(v_toFunctor_3118_);
lean_dec(v_toApplicative_3114_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3145_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___f_3125_; lean_object* v___f_3126_; lean_object* v___f_3127_; lean_object* v___f_3128_; lean_object* v___x_3129_; lean_object* v___f_3130_; lean_object* v___f_3131_; lean_object* v___f_3132_; lean_object* v___x_3134_; 
v___f_3125_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3));
v___f_3126_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4));
lean_inc_ref(v_toFunctor_3118_);
v___f_3127_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3127_, 0, v_toFunctor_3118_);
v___f_3128_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3128_, 0, v_toFunctor_3118_);
v___x_3129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___f_3127_);
lean_ctor_set(v___x_3129_, 1, v___f_3128_);
v___f_3130_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3130_, 0, v_toSeqRight_3121_);
v___f_3131_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3131_, 0, v_toSeqLeft_3120_);
v___f_3132_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3132_, 0, v_toSeq_3119_);
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 4, v___f_3130_);
lean_ctor_set(v___x_3123_, 3, v___f_3131_);
lean_ctor_set(v___x_3123_, 2, v___f_3132_);
lean_ctor_set(v___x_3123_, 1, v___f_3125_);
lean_ctor_set(v___x_3123_, 0, v___x_3129_);
v___x_3134_ = v___x_3123_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3129_);
lean_ctor_set(v_reuseFailAlloc_3144_, 1, v___f_3125_);
lean_ctor_set(v_reuseFailAlloc_3144_, 2, v___f_3132_);
lean_ctor_set(v_reuseFailAlloc_3144_, 3, v___f_3131_);
lean_ctor_set(v_reuseFailAlloc_3144_, 4, v___f_3130_);
v___x_3134_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
lean_object* v___x_3136_; 
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 1, v___f_3126_);
lean_ctor_set(v___x_3116_, 0, v___x_3134_);
v___x_3136_ = v___x_3116_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3134_);
lean_ctor_set(v_reuseFailAlloc_3143_, 1, v___f_3126_);
v___x_3136_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___f_3140_; lean_object* v___x_909__overap_3141_; lean_object* v___x_3142_; 
v___x_3137_ = l_StateRefT_x27_instMonad___redArg(v___x_3136_);
v___x_3138_ = l_Lean_instInhabitedExpr;
v___x_3139_ = l_instInhabitedOfMonad___redArg(v___x_3137_, v___x_3138_);
v___f_3140_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3140_, 0, v___x_3139_);
v___x_909__overap_3141_ = lean_panic_fn_borrowed(v___f_3140_, v_msg_3080_);
lean_dec_ref(v___f_3140_);
lean_inc(v___y_3086_);
lean_inc_ref(v___y_3085_);
lean_inc(v___y_3084_);
lean_inc_ref(v___y_3083_);
lean_inc(v___y_3082_);
lean_inc_ref(v___y_3081_);
v___x_3142_ = lean_apply_7(v___x_909__overap_3141_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, lean_box(0));
return v___x_3142_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___boxed(lean_object* v_msg_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(v_msg_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_3164_, lean_object* v_vals_3165_, lean_object* v_i_3166_, lean_object* v_k_3167_){
_start:
{
lean_object* v___x_3168_; uint8_t v___x_3169_; 
v___x_3168_ = lean_array_get_size(v_keys_3164_);
v___x_3169_ = lean_nat_dec_lt(v_i_3166_, v___x_3168_);
if (v___x_3169_ == 0)
{
lean_object* v___x_3170_; 
lean_dec_ref(v_k_3167_);
lean_dec(v_i_3166_);
v___x_3170_ = lean_box(0);
return v___x_3170_;
}
else
{
lean_object* v_k_x27_3171_; uint8_t v___x_3172_; 
v_k_x27_3171_ = lean_array_fget_borrowed(v_keys_3164_, v_i_3166_);
lean_inc(v_k_x27_3171_);
lean_inc_ref(v_k_3167_);
v___x_3172_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_3167_, v_k_x27_3171_);
if (v___x_3172_ == 0)
{
lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3173_ = lean_unsigned_to_nat(1u);
v___x_3174_ = lean_nat_add(v_i_3166_, v___x_3173_);
lean_dec(v_i_3166_);
v_i_3166_ = v___x_3174_;
goto _start;
}
else
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
lean_dec_ref(v_k_3167_);
v___x_3176_ = lean_array_fget_borrowed(v_vals_3165_, v_i_3166_);
lean_dec(v_i_3166_);
lean_inc(v___x_3176_);
lean_inc(v_k_x27_3171_);
v___x_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3177_, 0, v_k_x27_3171_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
v___x_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
return v___x_3178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_3179_, lean_object* v_vals_3180_, lean_object* v_i_3181_, lean_object* v_k_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_keys_3179_, v_vals_3180_, v_i_3181_, v_k_3182_);
lean_dec_ref(v_vals_3180_);
lean_dec_ref(v_keys_3179_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(lean_object* v_x_3184_, size_t v_x_3185_, lean_object* v_x_3186_){
_start:
{
if (lean_obj_tag(v_x_3184_) == 0)
{
lean_object* v_es_3187_; lean_object* v___x_3188_; size_t v___x_3189_; size_t v___x_3190_; lean_object* v_j_3191_; lean_object* v___x_3192_; 
v_es_3187_ = lean_ctor_get(v_x_3184_, 0);
lean_inc_ref(v_es_3187_);
lean_dec_ref_known(v_x_3184_, 1);
v___x_3188_ = lean_box(2);
v___x_3189_ = ((size_t)31ULL);
v___x_3190_ = lean_usize_land(v_x_3185_, v___x_3189_);
v_j_3191_ = lean_usize_to_nat(v___x_3190_);
v___x_3192_ = lean_array_get(v___x_3188_, v_es_3187_, v_j_3191_);
lean_dec(v_j_3191_);
lean_dec_ref(v_es_3187_);
switch(lean_obj_tag(v___x_3192_))
{
case 0:
{
lean_object* v_key_3193_; lean_object* v_val_3194_; uint8_t v___x_3195_; 
v_key_3193_ = lean_ctor_get(v___x_3192_, 0);
lean_inc_n(v_key_3193_, 2);
v_val_3194_ = lean_ctor_get(v___x_3192_, 1);
lean_inc(v_val_3194_);
lean_dec_ref_known(v___x_3192_, 2);
v___x_3195_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_3186_, v_key_3193_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; 
lean_dec(v_val_3194_);
lean_dec(v_key_3193_);
v___x_3196_ = lean_box(0);
return v___x_3196_;
}
else
{
lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3197_, 0, v_key_3193_);
lean_ctor_set(v___x_3197_, 1, v_val_3194_);
v___x_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3197_);
return v___x_3198_;
}
}
case 1:
{
lean_object* v_node_3199_; size_t v___x_3200_; size_t v___x_3201_; 
v_node_3199_ = lean_ctor_get(v___x_3192_, 0);
lean_inc(v_node_3199_);
lean_dec_ref_known(v___x_3192_, 1);
v___x_3200_ = ((size_t)5ULL);
v___x_3201_ = lean_usize_shift_right(v_x_3185_, v___x_3200_);
v_x_3184_ = v_node_3199_;
v_x_3185_ = v___x_3201_;
goto _start;
}
default: 
{
lean_object* v___x_3203_; 
lean_dec_ref(v_x_3186_);
v___x_3203_ = lean_box(0);
return v___x_3203_;
}
}
}
else
{
lean_object* v_ks_3204_; lean_object* v_vs_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v_ks_3204_ = lean_ctor_get(v_x_3184_, 0);
lean_inc_ref(v_ks_3204_);
v_vs_3205_ = lean_ctor_get(v_x_3184_, 1);
lean_inc_ref(v_vs_3205_);
lean_dec_ref_known(v_x_3184_, 2);
v___x_3206_ = lean_unsigned_to_nat(0u);
v___x_3207_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_ks_3204_, v_vs_3205_, v___x_3206_, v_x_3186_);
lean_dec_ref(v_vs_3205_);
lean_dec_ref(v_ks_3204_);
return v___x_3207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg___boxed(lean_object* v_x_3208_, lean_object* v_x_3209_, lean_object* v_x_3210_){
_start:
{
size_t v_x_1226__boxed_3211_; lean_object* v_res_3212_; 
v_x_1226__boxed_3211_ = lean_unbox_usize(v_x_3209_);
lean_dec(v_x_3209_);
v_res_3212_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3208_, v_x_1226__boxed_3211_, v_x_3210_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(lean_object* v_x_3213_, lean_object* v_x_3214_){
_start:
{
uint64_t v___x_3215_; size_t v___x_3216_; lean_object* v___x_3217_; 
v___x_3215_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_3214_);
v___x_3216_ = lean_uint64_to_usize(v___x_3215_);
lean_inc_ref(v_x_3213_);
v___x_3217_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3213_, v___x_3216_, v_x_3214_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg___boxed(lean_object* v_x_3218_, lean_object* v_x_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v_x_3218_, v_x_3219_);
lean_dec_ref(v_x_3218_);
return v_res_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0(lean_object* v_e_3221_, lean_object* v_cache_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
lean_object* v___x_3225_; 
lean_inc_ref(v_e_3221_);
v___x_3225_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v___y_3224_, v_e_3221_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3226_, 0, v_cache_3222_);
lean_ctor_set(v___x_3226_, 1, v___y_3224_);
v___x_3227_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_3221_, v___y_3223_, v___x_3226_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v_a_3228_; lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3237_; 
v_a_3228_ = lean_ctor_get(v___x_3227_, 1);
v_a_3229_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3231_ = v___x_3227_;
v_isShared_3232_ = v_isSharedCheck_3237_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3228_);
lean_inc(v_a_3229_);
lean_dec(v___x_3227_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3237_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v_set_3233_; lean_object* v___x_3235_; 
v_set_3233_ = lean_ctor_get(v_a_3228_, 1);
lean_inc_ref(v_set_3233_);
lean_dec(v_a_3228_);
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 1, v_set_3233_);
v___x_3235_ = v___x_3231_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3229_);
lean_ctor_set(v_reuseFailAlloc_3236_, 1, v_set_3233_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
else
{
lean_object* v_a_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3247_; 
v_a_3238_ = lean_ctor_get(v___x_3227_, 1);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3247_ == 0)
{
lean_object* v_unused_3248_; 
v_unused_3248_ = lean_ctor_get(v___x_3227_, 0);
lean_dec(v_unused_3248_);
v___x_3240_ = v___x_3227_;
v_isShared_3241_ = v_isSharedCheck_3247_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_a_3238_);
lean_dec(v___x_3227_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3247_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v_map_3242_; lean_object* v_set_3243_; lean_object* v___x_3245_; 
v_map_3242_ = lean_ctor_get(v_a_3238_, 0);
lean_inc_ref(v_map_3242_);
v_set_3243_ = lean_ctor_get(v_a_3238_, 1);
lean_inc_ref(v_set_3243_);
lean_dec(v_a_3238_);
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 1, v_set_3243_);
lean_ctor_set(v___x_3240_, 0, v_map_3242_);
v___x_3245_ = v___x_3240_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_map_3242_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v_set_3243_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
else
{
lean_object* v_val_3249_; lean_object* v_fst_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3257_; 
lean_dec_ref(v_cache_3222_);
lean_dec_ref(v_e_3221_);
v_val_3249_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_val_3249_);
lean_dec_ref_known(v___x_3225_, 1);
v_fst_3250_ = lean_ctor_get(v_val_3249_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v_val_3249_);
if (v_isSharedCheck_3257_ == 0)
{
lean_object* v_unused_3258_; 
v_unused_3258_ = lean_ctor_get(v_val_3249_, 1);
lean_dec(v_unused_3258_);
v___x_3252_ = v_val_3249_;
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_fst_3250_);
lean_dec(v_val_3249_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3255_; 
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 1, v___y_3224_);
v___x_3255_ = v___x_3252_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_fst_3250_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v___y_3224_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0___boxed(lean_object* v_e_3259_, lean_object* v_cache_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0(v_e_3259_, v_cache_3260_, v___y_3261_, v___y_3262_);
lean_dec_ref(v___y_3261_);
return v_res_3263_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1(void){
_start:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3265_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__6));
v___x_3266_ = lean_unsigned_to_nat(16u);
v___x_3267_ = lean_unsigned_to_nat(386u);
v___x_3268_ = ((lean_object*)(l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__0));
v___x_3269_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__4));
v___x_3270_ = l_mkPanicMessageWithDecl(v___x_3269_, v___x_3268_, v___x_3267_, v___x_3266_, v___x_3265_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks(lean_object* v_e_3271_, lean_object* v_cache_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_){
_start:
{
lean_object* v___x_3280_; lean_object* v_env_3281_; lean_object* v___f_3282_; uint8_t v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3296_; 
v___x_3280_ = lean_st_ref_get(v_a_3278_);
v_env_3281_ = lean_ctor_get(v___x_3280_, 0);
lean_inc_ref(v_env_3281_);
lean_dec(v___x_3280_);
v___f_3282_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3282_, 0, v_e_3271_);
lean_closure_set(v___f_3282_, 1, v_cache_3272_);
v___x_3283_ = 0;
v___x_3284_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3284_, 0, v_env_3281_);
lean_ctor_set_uint8(v___x_3284_, sizeof(void*)*1, v___x_3283_);
lean_ctor_set_uint8(v___x_3284_, sizeof(void*)*1 + 1, v___x_3283_);
v___x_3285_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3282_, v___x_3284_, v_a_3274_);
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3288_ = v___x_3285_;
v_isShared_3289_ = v_isSharedCheck_3296_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3285_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3296_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
if (lean_obj_tag(v_a_3286_) == 0)
{
lean_object* v___x_3290_; lean_object* v___x_3291_; 
lean_dec_ref_known(v_a_3286_, 1);
lean_del_object(v___x_3288_);
v___x_3290_ = lean_obj_once(&l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1, &l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1_once, _init_l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1);
v___x_3291_ = l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(v___x_3290_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
return v___x_3291_;
}
else
{
lean_object* v_a_3292_; lean_object* v___x_3294_; 
v_a_3292_ = lean_ctor_get(v_a_3286_, 0);
lean_inc(v_a_3292_);
lean_dec_ref_known(v_a_3286_, 1);
if (v_isShared_3289_ == 0)
{
lean_ctor_set(v___x_3288_, 0, v_a_3292_);
v___x_3294_ = v___x_3288_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3292_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___boxed(lean_object* v_e_3297_, lean_object* v_cache_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_Lean_Meta_Sym_shareCommonWithoutChecks(v_e_3297_, v_cache_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_);
lean_dec(v_a_3304_);
lean_dec_ref(v_a_3303_);
lean_dec(v_a_3302_);
lean_dec_ref(v_a_3301_);
lean_dec(v_a_3300_);
lean_dec_ref(v_a_3299_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0(lean_object* v_00_u03b2_3307_, lean_object* v_x_3308_, lean_object* v_x_3309_){
_start:
{
lean_object* v___x_3310_; 
v___x_3310_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v_x_3308_, v_x_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___boxed(lean_object* v_00_u03b2_3311_, lean_object* v_x_3312_, lean_object* v_x_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0(v_00_u03b2_3311_, v_x_3312_, v_x_3313_);
lean_dec_ref(v_x_3312_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0(lean_object* v_00_u03b2_3315_, lean_object* v_x_3316_, size_t v_x_3317_, lean_object* v_x_3318_){
_start:
{
lean_object* v___x_3319_; 
lean_inc_ref(v_x_3316_);
v___x_3319_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3316_, v_x_3317_, v_x_3318_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3320_, lean_object* v_x_3321_, lean_object* v_x_3322_, lean_object* v_x_3323_){
_start:
{
size_t v_x_1431__boxed_3324_; lean_object* v_res_3325_; 
v_x_1431__boxed_3324_ = lean_unbox_usize(v_x_3322_);
lean_dec(v_x_3322_);
v_res_3325_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0(v_00_u03b2_3320_, v_x_3321_, v_x_1431__boxed_3324_, v_x_3323_);
lean_dec_ref(v_x_3321_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3326_, lean_object* v_keys_3327_, lean_object* v_vals_3328_, lean_object* v_heq_3329_, lean_object* v_i_3330_, lean_object* v_k_3331_){
_start:
{
lean_object* v___x_3332_; 
v___x_3332_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_keys_3327_, v_vals_3328_, v_i_3330_, v_k_3331_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3333_, lean_object* v_keys_3334_, lean_object* v_vals_3335_, lean_object* v_heq_3336_, lean_object* v_i_3337_, lean_object* v_k_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2(v_00_u03b2_3333_, v_keys_3334_, v_vals_3335_, v_heq_3336_, v_i_3337_, v_k_3338_);
lean_dec_ref(v_vals_3335_);
lean_dec_ref(v_keys_3334_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(lean_object* v_msg_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
lean_object* v_ref_3346_; lean_object* v___x_3347_; lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3356_; 
v_ref_3346_ = lean_ctor_get(v___y_3343_, 5);
v___x_3347_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3350_ = v___x_3347_;
v_isShared_3351_ = v_isSharedCheck_3356_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3347_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3356_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3352_; lean_object* v___x_3354_; 
lean_inc(v_ref_3346_);
v___x_3352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3352_, 0, v_ref_3346_);
lean_ctor_set(v___x_3352_, 1, v_a_3348_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set_tag(v___x_3350_, 1);
lean_ctor_set(v___x_3350_, 0, v___x_3352_);
v___x_3354_ = v___x_3350_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3352_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg___boxed(lean_object* v_msg_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_){
_start:
{
lean_object* v_res_3363_; 
v_res_3363_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v_msg_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
lean_dec(v___y_3361_);
lean_dec_ref(v___y_3360_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
return v_res_3363_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1(void){
_start:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3365_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__0));
v___x_3366_ = l_Lean_stringToMessageData(v___x_3365_);
return v___x_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(lean_object* v_e_3367_, lean_object* v_cache_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_){
_start:
{
lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; uint8_t v___x_3386_; 
v___x_3386_ = l_Lean_Expr_hasLooseBVars(v_e_3367_);
if (v___x_3386_ == 0)
{
v___y_3377_ = v_a_3369_;
v___y_3378_ = v_a_3370_;
v___y_3379_ = v_a_3371_;
v___y_3380_ = v_a_3372_;
v___y_3381_ = v_a_3373_;
v___y_3382_ = v_a_3374_;
goto v___jp_3376_;
}
else
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
lean_dec_ref(v_cache_3368_);
v___x_3387_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1);
v___x_3388_ = l_Lean_indentExpr(v_e_3367_);
v___x_3389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3387_);
lean_ctor_set(v___x_3389_, 1, v___x_3388_);
v___x_3390_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v___x_3389_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3390_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3390_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
v___jp_3376_:
{
lean_object* v___x_3383_; 
v___x_3383_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3367_, v___y_3377_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v_a_3384_; lean_object* v___x_3385_; 
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
lean_inc(v_a_3384_);
lean_dec_ref_known(v___x_3383_, 1);
v___x_3385_ = l_Lean_Meta_Sym_shareCommonWithoutChecks(v_a_3384_, v_cache_3368_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
return v___x_3385_;
}
else
{
lean_dec_ref(v_cache_3368_);
return v___x_3383_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___boxed(lean_object* v_e_3399_, lean_object* v_cache_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3399_, v_cache_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_);
lean_dec(v_a_3406_);
lean_dec_ref(v_a_3405_);
lean_dec(v_a_3404_);
lean_dec_ref(v_a_3403_);
lean_dec(v_a_3402_);
lean_dec_ref(v_a_3401_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0(lean_object* v_00_u03b1_3409_, lean_object* v_msg_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v___x_3418_; 
v___x_3418_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v_msg_3410_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
return v___x_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___boxed(lean_object* v_00_u03b1_3419_, lean_object* v_msg_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0(v_00_u03b1_3419_, v_msg_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___lam__0(lean_object* v_e_3429_, lean_object* v___x_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v___x_3433_; 
lean_inc_ref(v_e_3429_);
v___x_3433_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v___y_3432_, v_e_3429_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3430_);
lean_ctor_set(v___x_3434_, 1, v___y_3432_);
v___x_3435_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_3429_, v___y_3431_, v___x_3434_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_a_3436_; lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3445_; 
v_a_3436_ = lean_ctor_get(v___x_3435_, 1);
v_a_3437_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3439_ = v___x_3435_;
v_isShared_3440_ = v_isSharedCheck_3445_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3436_);
lean_inc(v_a_3437_);
lean_dec(v___x_3435_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3445_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v_set_3441_; lean_object* v___x_3443_; 
v_set_3441_ = lean_ctor_get(v_a_3436_, 1);
lean_inc_ref(v_set_3441_);
lean_dec(v_a_3436_);
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 1, v_set_3441_);
v___x_3443_ = v___x_3439_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3437_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v_set_3441_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
else
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3455_; 
v_a_3446_ = lean_ctor_get(v___x_3435_, 1);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3455_ == 0)
{
lean_object* v_unused_3456_; 
v_unused_3456_ = lean_ctor_get(v___x_3435_, 0);
lean_dec(v_unused_3456_);
v___x_3448_ = v___x_3435_;
v_isShared_3449_ = v_isSharedCheck_3455_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3435_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3455_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v_map_3450_; lean_object* v_set_3451_; lean_object* v___x_3453_; 
v_map_3450_ = lean_ctor_get(v_a_3446_, 0);
lean_inc_ref(v_map_3450_);
v_set_3451_ = lean_ctor_get(v_a_3446_, 1);
lean_inc_ref(v_set_3451_);
lean_dec(v_a_3446_);
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 1, v_set_3451_);
lean_ctor_set(v___x_3448_, 0, v_map_3450_);
v___x_3453_ = v___x_3448_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_map_3450_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v_set_3451_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
}
else
{
lean_object* v_val_3457_; lean_object* v_fst_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3465_; 
lean_dec_ref(v___x_3430_);
lean_dec_ref(v_e_3429_);
v_val_3457_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_val_3457_);
lean_dec_ref_known(v___x_3433_, 1);
v_fst_3458_ = lean_ctor_get(v_val_3457_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v_val_3457_);
if (v_isSharedCheck_3465_ == 0)
{
lean_object* v_unused_3466_; 
v_unused_3466_ = lean_ctor_get(v_val_3457_, 1);
lean_dec(v_unused_3466_);
v___x_3460_ = v_val_3457_;
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_fst_3458_);
lean_dec(v_val_3457_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3463_; 
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 1, v___y_3432_);
v___x_3463_ = v___x_3460_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_fst_3458_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v___y_3432_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___lam__0___boxed(lean_object* v_e_3467_, lean_object* v___x_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v_res_3471_; 
v_res_3471_ = l_Lean_Meta_Sym_shareCommon___lam__0(v_e_3467_, v___x_3468_, v___y_3469_, v___y_3470_);
lean_dec_ref(v___y_3469_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon(lean_object* v_e_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_){
_start:
{
lean_object* v___x_3480_; lean_object* v_a_3481_; lean_object* v___x_3482_; lean_object* v___f_3483_; lean_object* v___x_3484_; lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3495_; 
v___x_3480_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3473_, v_a_3478_);
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
lean_inc(v_a_3481_);
lean_dec_ref(v___x_3480_);
v___x_3482_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
lean_inc_ref(v_e_3472_);
v___f_3483_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommon___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3483_, 0, v_e_3472_);
lean_closure_set(v___f_3483_, 1, v___x_3482_);
v___x_3484_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3483_, v_a_3481_, v_a_3474_);
v_a_3485_ = lean_ctor_get(v___x_3484_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3487_ = v___x_3484_;
v_isShared_3488_ = v_isSharedCheck_3495_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3484_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3495_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
if (lean_obj_tag(v_a_3485_) == 0)
{
lean_object* v_a_3489_; lean_object* v___x_3490_; 
lean_del_object(v___x_3487_);
v_a_3489_ = lean_ctor_get(v_a_3485_, 0);
lean_inc(v_a_3489_);
lean_dec_ref_known(v_a_3485_, 1);
v___x_3490_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3472_, v_a_3489_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
return v___x_3490_;
}
else
{
lean_object* v_a_3491_; lean_object* v___x_3493_; 
lean_dec_ref(v_e_3472_);
v_a_3491_ = lean_ctor_get(v_a_3485_, 0);
lean_inc(v_a_3491_);
lean_dec_ref_known(v_a_3485_, 1);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 0, v_a_3491_);
v___x_3493_ = v___x_3487_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3491_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___boxed(lean_object* v_e_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_){
_start:
{
lean_object* v_res_3504_; 
v_res_3504_ = l_Lean_Meta_Sym_shareCommon(v_e_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_);
lean_dec(v_a_3502_);
lean_dec_ref(v_a_3501_);
lean_dec(v_a_3500_);
lean_dec_ref(v_a_3499_);
lean_dec(v_a_3498_);
lean_dec_ref(v_a_3497_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___lam__0(lean_object* v_e_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_3505_, v___y_3506_, v___y_3507_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___lam__0___boxed(lean_object* v_e_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
lean_object* v_res_3512_; 
v_res_3512_ = l_Lean_Meta_Sym_shareCommonInc___lam__0(v_e_3509_, v___y_3510_, v___y_3511_);
lean_dec_ref(v___y_3510_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object* v_e_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_){
_start:
{
lean_object* v___x_3521_; lean_object* v_a_3522_; lean_object* v___f_3523_; lean_object* v___x_3524_; lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3535_; 
v___x_3521_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3514_, v_a_3519_);
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3522_);
lean_dec_ref(v___x_3521_);
lean_inc_ref(v_e_3513_);
v___f_3523_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommonInc___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3523_, 0, v_e_3513_);
v___x_3524_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3523_, v_a_3522_, v_a_3515_);
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3527_ = v___x_3524_;
v_isShared_3528_ = v_isSharedCheck_3535_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3524_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3535_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
if (lean_obj_tag(v_a_3525_) == 0)
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
lean_dec_ref_known(v_a_3525_, 1);
lean_del_object(v___x_3527_);
v___x_3529_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_3530_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3513_, v___x_3529_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_);
return v___x_3530_;
}
else
{
lean_object* v_a_3531_; lean_object* v___x_3533_; 
lean_dec_ref(v_e_3513_);
v_a_3531_ = lean_ctor_get(v_a_3525_, 0);
lean_inc(v_a_3531_);
lean_dec_ref_known(v_a_3525_, 1);
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 0, v_a_3531_);
v___x_3533_ = v___x_3527_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3531_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___boxed(lean_object* v_e_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_Lean_Meta_Sym_shareCommonInc(v_e_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
lean_dec(v_a_3542_);
lean_dec_ref(v_a_3541_);
lean_dec(v_a_3540_);
lean_dec_ref(v_a_3539_);
lean_dec(v_a_3538_);
lean_dec_ref(v_a_3537_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share(lean_object* v_e_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_){
_start:
{
lean_object* v___x_3553_; 
v___x_3553_ = l_Lean_Meta_Sym_shareCommonInc(v_e_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_);
return v___x_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___boxed(lean_object* v_e_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l_Lean_Meta_Sym_share(v_e_3554_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_);
lean_dec(v_a_3560_);
lean_dec_ref(v_a_3559_);
lean_dec(v_a_3558_);
lean_dec_ref(v_a_3557_);
lean_dec(v_a_3556_);
lean_dec_ref(v_a_3555_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg(lean_object* v_a_3563_){
_start:
{
lean_object* v___x_3565_; uint8_t v_debug_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3565_ = lean_st_ref_get(v_a_3563_);
v_debug_3566_ = lean_ctor_get_uint8(v___x_3565_, sizeof(void*)*10);
lean_dec(v___x_3565_);
v___x_3567_ = lean_box(v_debug_3566_);
v___x_3568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3567_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg___boxed(lean_object* v_a_3569_, lean_object* v_a_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l_Lean_Meta_Sym_isDebugEnabled___redArg(v_a_3569_);
lean_dec(v_a_3569_);
return v_res_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled(lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_){
_start:
{
lean_object* v___x_3579_; uint8_t v_debug_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3579_ = lean_st_ref_get(v_a_3573_);
v_debug_3580_ = lean_ctor_get_uint8(v___x_3579_, sizeof(void*)*10);
lean_dec(v___x_3579_);
v___x_3581_ = lean_box(v_debug_3580_);
v___x_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3581_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___boxed(lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l_Lean_Meta_Sym_isDebugEnabled(v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_);
lean_dec(v_a_3588_);
lean_dec_ref(v_a_3587_);
lean_dec(v_a_3586_);
lean_dec_ref(v_a_3585_);
lean_dec(v_a_3584_);
lean_dec_ref(v_a_3583_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object* v_a_3591_){
_start:
{
lean_object* v_config_3593_; lean_object* v___x_3594_; 
v_config_3593_ = lean_ctor_get(v_a_3591_, 1);
lean_inc_ref(v_config_3593_);
v___x_3594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3594_, 0, v_config_3593_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg___boxed(lean_object* v_a_3595_, lean_object* v_a_3596_){
_start:
{
lean_object* v_res_3597_; 
v_res_3597_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3595_);
lean_dec_ref(v_a_3595_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig(lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_){
_start:
{
lean_object* v___x_3605_; 
v___x_3605_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3598_);
return v___x_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___boxed(lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_){
_start:
{
lean_object* v_res_3613_; 
v_res_3613_ = l_Lean_Meta_Sym_getConfig(v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_);
lean_dec(v_a_3611_);
lean_dec_ref(v_a_3610_);
lean_dec(v_a_3609_);
lean_dec_ref(v_a_3608_);
lean_dec(v_a_3607_);
lean_dec_ref(v_a_3606_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(lean_object* v_cls_3614_, lean_object* v_msg_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
lean_object* v_ref_3621_; lean_object* v___x_3622_; lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3667_; 
v_ref_3621_ = lean_ctor_get(v___y_3618_, 5);
v___x_3622_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_);
v_a_3623_ = lean_ctor_get(v___x_3622_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3625_ = v___x_3622_;
v_isShared_3626_ = v_isSharedCheck_3667_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3622_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3667_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3627_; lean_object* v_traceState_3628_; lean_object* v_env_3629_; lean_object* v_nextMacroScope_3630_; lean_object* v_ngen_3631_; lean_object* v_auxDeclNGen_3632_; lean_object* v_cache_3633_; lean_object* v_messages_3634_; lean_object* v_infoState_3635_; lean_object* v_snapshotTasks_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3666_; 
v___x_3627_ = lean_st_ref_take(v___y_3619_);
v_traceState_3628_ = lean_ctor_get(v___x_3627_, 4);
v_env_3629_ = lean_ctor_get(v___x_3627_, 0);
v_nextMacroScope_3630_ = lean_ctor_get(v___x_3627_, 1);
v_ngen_3631_ = lean_ctor_get(v___x_3627_, 2);
v_auxDeclNGen_3632_ = lean_ctor_get(v___x_3627_, 3);
v_cache_3633_ = lean_ctor_get(v___x_3627_, 5);
v_messages_3634_ = lean_ctor_get(v___x_3627_, 6);
v_infoState_3635_ = lean_ctor_get(v___x_3627_, 7);
v_snapshotTasks_3636_ = lean_ctor_get(v___x_3627_, 8);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3638_ = v___x_3627_;
v_isShared_3639_ = v_isSharedCheck_3666_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_snapshotTasks_3636_);
lean_inc(v_infoState_3635_);
lean_inc(v_messages_3634_);
lean_inc(v_cache_3633_);
lean_inc(v_traceState_3628_);
lean_inc(v_auxDeclNGen_3632_);
lean_inc(v_ngen_3631_);
lean_inc(v_nextMacroScope_3630_);
lean_inc(v_env_3629_);
lean_dec(v___x_3627_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3666_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
uint64_t v_tid_3640_; lean_object* v_traces_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3665_; 
v_tid_3640_ = lean_ctor_get_uint64(v_traceState_3628_, sizeof(void*)*1);
v_traces_3641_ = lean_ctor_get(v_traceState_3628_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v_traceState_3628_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3643_ = v_traceState_3628_;
v_isShared_3644_ = v_isSharedCheck_3665_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_traces_3641_);
lean_dec(v_traceState_3628_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3665_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3645_; double v___x_3646_; uint8_t v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3655_; 
v___x_3645_ = lean_box(0);
v___x_3646_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_3647_ = 0;
v___x_3648_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_3649_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3649_, 0, v_cls_3614_);
lean_ctor_set(v___x_3649_, 1, v___x_3645_);
lean_ctor_set(v___x_3649_, 2, v___x_3648_);
lean_ctor_set_float(v___x_3649_, sizeof(void*)*3, v___x_3646_);
lean_ctor_set_float(v___x_3649_, sizeof(void*)*3 + 8, v___x_3646_);
lean_ctor_set_uint8(v___x_3649_, sizeof(void*)*3 + 16, v___x_3647_);
v___x_3650_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
v___x_3651_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3649_);
lean_ctor_set(v___x_3651_, 1, v_a_3623_);
lean_ctor_set(v___x_3651_, 2, v___x_3650_);
lean_inc(v_ref_3621_);
v___x_3652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3652_, 0, v_ref_3621_);
lean_ctor_set(v___x_3652_, 1, v___x_3651_);
v___x_3653_ = l_Lean_PersistentArray_push___redArg(v_traces_3641_, v___x_3652_);
if (v_isShared_3644_ == 0)
{
lean_ctor_set(v___x_3643_, 0, v___x_3653_);
v___x_3655_ = v___x_3643_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3653_);
lean_ctor_set_uint64(v_reuseFailAlloc_3664_, sizeof(void*)*1, v_tid_3640_);
v___x_3655_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
lean_object* v___x_3657_; 
if (v_isShared_3639_ == 0)
{
lean_ctor_set(v___x_3638_, 4, v___x_3655_);
v___x_3657_ = v___x_3638_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_env_3629_);
lean_ctor_set(v_reuseFailAlloc_3663_, 1, v_nextMacroScope_3630_);
lean_ctor_set(v_reuseFailAlloc_3663_, 2, v_ngen_3631_);
lean_ctor_set(v_reuseFailAlloc_3663_, 3, v_auxDeclNGen_3632_);
lean_ctor_set(v_reuseFailAlloc_3663_, 4, v___x_3655_);
lean_ctor_set(v_reuseFailAlloc_3663_, 5, v_cache_3633_);
lean_ctor_set(v_reuseFailAlloc_3663_, 6, v_messages_3634_);
lean_ctor_set(v_reuseFailAlloc_3663_, 7, v_infoState_3635_);
lean_ctor_set(v_reuseFailAlloc_3663_, 8, v_snapshotTasks_3636_);
v___x_3657_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3661_; 
v___x_3658_ = lean_st_ref_set(v___y_3619_, v___x_3657_);
v___x_3659_ = lean_box(0);
if (v_isShared_3626_ == 0)
{
lean_ctor_set(v___x_3625_, 0, v___x_3659_);
v___x_3661_ = v___x_3625_;
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg___boxed(lean_object* v_cls_3668_, lean_object* v_msg_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_){
_start:
{
lean_object* v_res_3675_; 
v_res_3675_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v_cls_3668_, v_msg_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_);
lean_dec(v___y_3673_);
lean_dec_ref(v___y_3672_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
return v_res_3675_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_reportIssue___closed__2(void){
_start:
{
lean_object* v___x_3679_; uint8_t v___x_3680_; double v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___x_3679_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_3680_ = 1;
v___x_3681_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_3682_ = lean_box(0);
v___x_3683_ = ((lean_object*)(l_Lean_Meta_Sym_reportIssue___closed__1));
v___x_3684_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3684_, 0, v___x_3683_);
lean_ctor_set(v___x_3684_, 1, v___x_3682_);
lean_ctor_set(v___x_3684_, 2, v___x_3679_);
lean_ctor_set_float(v___x_3684_, sizeof(void*)*3, v___x_3681_);
lean_ctor_set_float(v___x_3684_, sizeof(void*)*3 + 8, v___x_3681_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*3 + 16, v___x_3680_);
return v___x_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue(lean_object* v_msg_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_){
_start:
{
lean_object* v___x_3696_; lean_object* v_a_3697_; lean_object* v___x_3698_; lean_object* v_share_3699_; lean_object* v_maxFVar_3700_; lean_object* v_proofInstInfo_3701_; lean_object* v_inferType_3702_; lean_object* v_getLevel_3703_; lean_object* v_congrInfo_3704_; lean_object* v_defEqI_3705_; lean_object* v_extensions_3706_; lean_object* v_issues_3707_; lean_object* v_canon_3708_; uint8_t v_debug_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3728_; 
v___x_3696_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3685_, v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_);
v_a_3697_ = lean_ctor_get(v___x_3696_, 0);
lean_inc(v_a_3697_);
lean_dec_ref(v___x_3696_);
v___x_3698_ = lean_st_ref_take(v_a_3687_);
v_share_3699_ = lean_ctor_get(v___x_3698_, 0);
v_maxFVar_3700_ = lean_ctor_get(v___x_3698_, 1);
v_proofInstInfo_3701_ = lean_ctor_get(v___x_3698_, 2);
v_inferType_3702_ = lean_ctor_get(v___x_3698_, 3);
v_getLevel_3703_ = lean_ctor_get(v___x_3698_, 4);
v_congrInfo_3704_ = lean_ctor_get(v___x_3698_, 5);
v_defEqI_3705_ = lean_ctor_get(v___x_3698_, 6);
v_extensions_3706_ = lean_ctor_get(v___x_3698_, 7);
v_issues_3707_ = lean_ctor_get(v___x_3698_, 8);
v_canon_3708_ = lean_ctor_get(v___x_3698_, 9);
v_debug_3709_ = lean_ctor_get_uint8(v___x_3698_, sizeof(void*)*10);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3711_ = v___x_3698_;
v_isShared_3712_ = v_isSharedCheck_3728_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_canon_3708_);
lean_inc(v_issues_3707_);
lean_inc(v_extensions_3706_);
lean_inc(v_defEqI_3705_);
lean_inc(v_congrInfo_3704_);
lean_inc(v_getLevel_3703_);
lean_inc(v_inferType_3702_);
lean_inc(v_proofInstInfo_3701_);
lean_inc(v_maxFVar_3700_);
lean_inc(v_share_3699_);
lean_dec(v___x_3698_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3728_;
goto v_resetjp_3710_;
}
v___jp_3693_:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3694_ = lean_box(0);
v___x_3695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3694_);
return v___x_3695_;
}
v_resetjp_3710_:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3718_; 
v___x_3713_ = lean_obj_once(&l_Lean_Meta_Sym_reportIssue___closed__2, &l_Lean_Meta_Sym_reportIssue___closed__2_once, _init_l_Lean_Meta_Sym_reportIssue___closed__2);
v___x_3714_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
lean_inc(v_a_3697_);
v___x_3715_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3713_);
lean_ctor_set(v___x_3715_, 1, v_a_3697_);
lean_ctor_set(v___x_3715_, 2, v___x_3714_);
v___x_3716_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3715_);
lean_ctor_set(v___x_3716_, 1, v_issues_3707_);
if (v_isShared_3712_ == 0)
{
lean_ctor_set(v___x_3711_, 8, v___x_3716_);
v___x_3718_ = v___x_3711_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_share_3699_);
lean_ctor_set(v_reuseFailAlloc_3727_, 1, v_maxFVar_3700_);
lean_ctor_set(v_reuseFailAlloc_3727_, 2, v_proofInstInfo_3701_);
lean_ctor_set(v_reuseFailAlloc_3727_, 3, v_inferType_3702_);
lean_ctor_set(v_reuseFailAlloc_3727_, 4, v_getLevel_3703_);
lean_ctor_set(v_reuseFailAlloc_3727_, 5, v_congrInfo_3704_);
lean_ctor_set(v_reuseFailAlloc_3727_, 6, v_defEqI_3705_);
lean_ctor_set(v_reuseFailAlloc_3727_, 7, v_extensions_3706_);
lean_ctor_set(v_reuseFailAlloc_3727_, 8, v___x_3716_);
lean_ctor_set(v_reuseFailAlloc_3727_, 9, v_canon_3708_);
lean_ctor_set_uint8(v_reuseFailAlloc_3727_, sizeof(void*)*10, v_debug_3709_);
v___x_3718_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
lean_object* v___x_3719_; lean_object* v_options_3720_; uint8_t v_hasTrace_3721_; 
v___x_3719_ = lean_st_ref_set(v_a_3687_, v___x_3718_);
v_options_3720_ = lean_ctor_get(v_a_3690_, 2);
v_hasTrace_3721_ = lean_ctor_get_uint8(v_options_3720_, sizeof(void*)*1);
if (v_hasTrace_3721_ == 0)
{
lean_dec(v_a_3697_);
goto v___jp_3693_;
}
else
{
lean_object* v_inheritedTraceOptions_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; uint8_t v___x_3725_; 
v_inheritedTraceOptions_3722_ = lean_ctor_get(v_a_3690_, 13);
v___x_3723_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_3724_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__2);
v___x_3725_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3722_, v_options_3720_, v___x_3724_);
if (v___x_3725_ == 0)
{
lean_dec(v_a_3697_);
goto v___jp_3693_;
}
else
{
lean_object* v___x_3726_; 
v___x_3726_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v___x_3723_, v_a_3697_, v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_);
return v___x_3726_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue___boxed(lean_object* v_msg_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l_Lean_Meta_Sym_reportIssue(v_msg_3729_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
lean_dec(v_a_3735_);
lean_dec_ref(v_a_3734_);
lean_dec(v_a_3733_);
lean_dec_ref(v_a_3732_);
lean_dec(v_a_3731_);
lean_dec_ref(v_a_3730_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0(lean_object* v_cls_3738_, lean_object* v_msg_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
lean_object* v___x_3747_; 
v___x_3747_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v_cls_3738_, v_msg_3739_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___boxed(lean_object* v_cls_3748_, lean_object* v_msg_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v_res_3757_; 
v_res_3757_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0(v_cls_3748_, v_msg_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose(lean_object* v_msg_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_){
_start:
{
lean_object* v___x_3766_; lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3777_; 
v___x_3766_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3759_);
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3769_ = v___x_3766_;
v_isShared_3770_ = v_isSharedCheck_3777_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3766_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3777_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
uint8_t v_verbose_3771_; 
v_verbose_3771_ = lean_ctor_get_uint8(v_a_3767_, 0);
lean_dec(v_a_3767_);
if (v_verbose_3771_ == 0)
{
lean_object* v___x_3772_; lean_object* v___x_3774_; 
lean_dec_ref(v_msg_3758_);
v___x_3772_ = lean_box(0);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 0, v___x_3772_);
v___x_3774_ = v___x_3769_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3772_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
else
{
lean_object* v___x_3776_; 
lean_del_object(v___x_3769_);
v___x_3776_ = l_Lean_Meta_Sym_reportIssue(v_msg_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_);
return v___x_3776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose___boxed(lean_object* v_msg_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_){
_start:
{
lean_object* v_res_3786_; 
v_res_3786_ = l_Lean_Meta_Sym_reportIssueIfVerbose(v_msg_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_);
lean_dec(v_a_3784_);
lean_dec_ref(v_a_3783_);
lean_dec(v_a_3782_);
lean_dec_ref(v_a_3781_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
return v_res_3786_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7(void){
_start:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3802_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6));
v___x_3803_ = l_String_toRawSubstring_x27(v___x_3802_);
return v___x_3803_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24(void){
_start:
{
lean_object* v___x_3841_; lean_object* v___x_3842_; 
v___x_3841_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_3842_ = l_String_toRawSubstring_x27(v___x_3841_);
return v___x_3842_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30(void){
_start:
{
lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3854_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29));
v___x_3855_ = l_String_toRawSubstring_x27(v___x_3854_);
return v___x_3855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(lean_object* v_s_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_){
_start:
{
lean_object* v_msg_3882_; lean_object* v_quotContext_3883_; lean_object* v_currMacroScope_3884_; lean_object* v_ref_3885_; lean_object* v___y_3886_; lean_object* v___x_3901_; lean_object* v___x_3902_; uint8_t v___x_3903_; 
lean_inc(v_s_3878_);
v___x_3901_ = l_Lean_Syntax_getKind(v_s_3878_);
v___x_3902_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16));
v___x_3903_ = lean_name_eq(v___x_3901_, v___x_3902_);
lean_dec(v___x_3901_);
if (v___x_3903_ == 0)
{
lean_object* v_quotContext_3904_; lean_object* v_currMacroScope_3905_; lean_object* v_ref_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v_quotContext_3904_ = lean_ctor_get(v_a_3879_, 1);
v_currMacroScope_3905_ = lean_ctor_get(v_a_3879_, 2);
v_ref_3906_ = lean_ctor_get(v_a_3879_, 5);
v___x_3907_ = l_Lean_SourceInfo_fromRef(v_ref_3906_, v___x_3903_);
v___x_3908_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18));
v___x_3909_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20));
v___x_3910_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21));
lean_inc_n(v___x_3907_, 8);
v___x_3911_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3907_);
lean_ctor_set(v___x_3911_, 1, v___x_3910_);
v___x_3912_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23));
v___x_3913_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
v___x_3914_ = lean_box(0);
lean_inc_n(v_currMacroScope_3905_, 3);
lean_inc_n(v_quotContext_3904_, 3);
v___x_3915_ = l_Lean_addMacroScope(v_quotContext_3904_, v___x_3914_, v_currMacroScope_3905_);
v___x_3916_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27));
v___x_3917_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3907_);
lean_ctor_set(v___x_3917_, 1, v___x_3913_);
lean_ctor_set(v___x_3917_, 2, v___x_3915_);
lean_ctor_set(v___x_3917_, 3, v___x_3916_);
v___x_3918_ = l_Lean_Syntax_node1(v___x_3907_, v___x_3912_, v___x_3917_);
v___x_3919_ = l_Lean_Syntax_node2(v___x_3907_, v___x_3909_, v___x_3911_, v___x_3918_);
v___x_3920_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28));
v___x_3921_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3907_);
lean_ctor_set(v___x_3921_, 1, v___x_3920_);
v___x_3922_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_3923_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
v___x_3924_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31));
v___x_3925_ = l_Lean_addMacroScope(v_quotContext_3904_, v___x_3924_, v_currMacroScope_3905_);
v___x_3926_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36));
v___x_3927_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3907_);
lean_ctor_set(v___x_3927_, 1, v___x_3923_);
lean_ctor_set(v___x_3927_, 2, v___x_3925_);
lean_ctor_set(v___x_3927_, 3, v___x_3926_);
v___x_3928_ = l_Lean_Syntax_node1(v___x_3907_, v___x_3922_, v___x_3927_);
v___x_3929_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37));
v___x_3930_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3907_);
lean_ctor_set(v___x_3930_, 1, v___x_3929_);
v___x_3931_ = l_Lean_Syntax_node5(v___x_3907_, v___x_3908_, v___x_3919_, v_s_3878_, v___x_3921_, v___x_3928_, v___x_3930_);
v_msg_3882_ = v___x_3931_;
v_quotContext_3883_ = v_quotContext_3904_;
v_currMacroScope_3884_ = v_currMacroScope_3905_;
v_ref_3885_ = v_ref_3906_;
v___y_3886_ = v_a_3880_;
goto v___jp_3881_;
}
else
{
lean_object* v_quotContext_3932_; lean_object* v_currMacroScope_3933_; lean_object* v_ref_3934_; uint8_t v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
v_quotContext_3932_ = lean_ctor_get(v_a_3879_, 1);
v_currMacroScope_3933_ = lean_ctor_get(v_a_3879_, 2);
v_ref_3934_ = lean_ctor_get(v_a_3879_, 5);
v___x_3935_ = 0;
v___x_3936_ = l_Lean_SourceInfo_fromRef(v_ref_3934_, v___x_3935_);
v___x_3937_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39));
v___x_3938_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40));
lean_inc(v___x_3936_);
v___x_3939_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3936_);
lean_ctor_set(v___x_3939_, 1, v___x_3938_);
v___x_3940_ = l_Lean_Syntax_node2(v___x_3936_, v___x_3937_, v___x_3939_, v_s_3878_);
lean_inc(v_currMacroScope_3933_);
lean_inc(v_quotContext_3932_);
v_msg_3882_ = v___x_3940_;
v_quotContext_3883_ = v_quotContext_3932_;
v_currMacroScope_3884_ = v_currMacroScope_3933_;
v_ref_3885_ = v_ref_3934_;
v___y_3886_ = v_a_3880_;
goto v___jp_3881_;
}
v___jp_3881_:
{
uint8_t v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3887_ = 0;
v___x_3888_ = l_Lean_SourceInfo_fromRef(v_ref_3885_, v___x_3887_);
v___x_3889_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3));
v___x_3890_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5));
v___x_3891_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7);
v___x_3892_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9));
v___x_3893_ = l_Lean_addMacroScope(v_quotContext_3883_, v___x_3892_, v_currMacroScope_3884_);
v___x_3894_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12));
lean_inc_n(v___x_3888_, 3);
v___x_3895_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3888_);
lean_ctor_set(v___x_3895_, 1, v___x_3891_);
lean_ctor_set(v___x_3895_, 2, v___x_3893_);
lean_ctor_set(v___x_3895_, 3, v___x_3894_);
v___x_3896_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_3897_ = l_Lean_Syntax_node1(v___x_3888_, v___x_3896_, v_msg_3882_);
v___x_3898_ = l_Lean_Syntax_node2(v___x_3888_, v___x_3890_, v___x_3895_, v___x_3897_);
v___x_3899_ = l_Lean_Syntax_node1(v___x_3888_, v___x_3889_, v___x_3898_);
v___x_3900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3899_);
lean_ctor_set(v___x_3900_, 1, v___y_3886_);
return v___x_3900_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___boxed(lean_object* v_s_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_){
_start:
{
lean_object* v_res_3944_; 
v_res_3944_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(v_s_3941_, v_a_3942_, v_a_3943_);
lean_dec_ref(v_a_3942_);
return v_res_3944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(lean_object* v_x_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_){
_start:
{
lean_object* v___x_3988_; uint8_t v___x_3989_; 
v___x_3988_ = ((lean_object*)(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1));
lean_inc(v_x_3985_);
v___x_3989_ = l_Lean_Syntax_isOfKind(v_x_3985_, v___x_3988_);
if (v___x_3989_ == 0)
{
lean_object* v___x_3990_; lean_object* v___x_3991_; 
lean_dec(v_x_3985_);
v___x_3990_ = lean_box(1);
v___x_3991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3990_);
lean_ctor_set(v___x_3991_, 1, v_a_3987_);
return v___x_3991_;
}
else
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v_a_3995_; lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4003_; 
v___x_3992_ = lean_unsigned_to_nat(1u);
v___x_3993_ = l_Lean_Syntax_getArg(v_x_3985_, v___x_3992_);
lean_dec(v_x_3985_);
v___x_3994_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(v___x_3993_, v_a_3986_, v_a_3987_);
v_a_3995_ = lean_ctor_get(v___x_3994_, 0);
v_a_3996_ = lean_ctor_get(v___x_3994_, 1);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3998_ = v___x_3994_;
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_inc(v_a_3995_);
lean_dec(v___x_3994_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4001_; 
if (v_isShared_3999_ == 0)
{
v___x_4001_ = v___x_3998_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3995_);
lean_ctor_set(v_reuseFailAlloc_4002_, 1, v_a_3996_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1___boxed(lean_object* v_x_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(v_x_4004_, v_a_4005_, v_a_4006_);
lean_dec_ref(v_a_4005_);
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue(lean_object* v_msg_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_){
_start:
{
lean_object* v___x_4016_; lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4036_; 
v___x_4016_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4009_);
v_a_4017_ = lean_ctor_get(v___x_4016_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4019_ = v___x_4016_;
v_isShared_4020_ = v_isSharedCheck_4036_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_4016_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4036_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
uint8_t v_verbose_4021_; 
v_verbose_4021_ = lean_ctor_get_uint8(v_a_4017_, 0);
lean_dec(v_a_4017_);
if (v_verbose_4021_ == 0)
{
lean_object* v___x_4022_; lean_object* v___x_4024_; 
lean_dec_ref(v_msg_4008_);
v___x_4022_ = lean_box(0);
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 0, v___x_4022_);
v___x_4024_ = v___x_4019_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v___x_4022_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
return v___x_4024_;
}
}
else
{
lean_object* v_options_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; uint8_t v___x_4030_; 
v_options_4026_ = lean_ctor_get(v_a_4013_, 2);
v___x_4027_ = l_Lean_KVMap_instValueBool;
v___x_4028_ = l_Lean_Meta_Sym_sym_debug;
v___x_4029_ = l_Lean_Option_get___redArg(v___x_4027_, v_options_4026_, v___x_4028_);
v___x_4030_ = lean_unbox(v___x_4029_);
lean_dec(v___x_4029_);
if (v___x_4030_ == 0)
{
lean_object* v___x_4031_; lean_object* v___x_4033_; 
lean_dec_ref(v_msg_4008_);
v___x_4031_ = lean_box(0);
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 0, v___x_4031_);
v___x_4033_ = v___x_4019_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v___x_4031_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
else
{
lean_object* v___x_4035_; 
lean_del_object(v___x_4019_);
v___x_4035_ = l_Lean_Meta_Sym_reportIssue(v_msg_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_);
return v___x_4035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue___boxed(lean_object* v_msg_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_){
_start:
{
lean_object* v_res_4045_; 
v_res_4045_ = l_Lean_Meta_Sym_reportDbgIssue(v_msg_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
lean_dec(v_a_4043_);
lean_dec_ref(v_a_4042_);
lean_dec(v_a_4041_);
lean_dec_ref(v_a_4040_);
lean_dec(v_a_4039_);
lean_dec_ref(v_a_4038_);
return v_res_4045_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1(void){
_start:
{
lean_object* v___x_4047_; lean_object* v___x_4048_; 
v___x_4047_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0));
v___x_4048_ = l_String_toRawSubstring_x27(v___x_4047_);
return v___x_4048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro(lean_object* v_s_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_){
_start:
{
lean_object* v_msg_4068_; lean_object* v_quotContext_4069_; lean_object* v_currMacroScope_4070_; lean_object* v_ref_4071_; lean_object* v___y_4072_; lean_object* v___x_4087_; lean_object* v___x_4088_; uint8_t v___x_4089_; 
lean_inc(v_s_4064_);
v___x_4087_ = l_Lean_Syntax_getKind(v_s_4064_);
v___x_4088_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16));
v___x_4089_ = lean_name_eq(v___x_4087_, v___x_4088_);
lean_dec(v___x_4087_);
if (v___x_4089_ == 0)
{
lean_object* v_quotContext_4090_; lean_object* v_currMacroScope_4091_; lean_object* v_ref_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v_quotContext_4090_ = lean_ctor_get(v_a_4065_, 1);
v_currMacroScope_4091_ = lean_ctor_get(v_a_4065_, 2);
v_ref_4092_ = lean_ctor_get(v_a_4065_, 5);
v___x_4093_ = l_Lean_SourceInfo_fromRef(v_ref_4092_, v___x_4089_);
v___x_4094_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18));
v___x_4095_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20));
v___x_4096_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21));
lean_inc_n(v___x_4093_, 8);
v___x_4097_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4093_);
lean_ctor_set(v___x_4097_, 1, v___x_4096_);
v___x_4098_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23));
v___x_4099_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
v___x_4100_ = lean_box(0);
lean_inc_n(v_currMacroScope_4091_, 3);
lean_inc_n(v_quotContext_4090_, 3);
v___x_4101_ = l_Lean_addMacroScope(v_quotContext_4090_, v___x_4100_, v_currMacroScope_4091_);
v___x_4102_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27));
v___x_4103_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4103_, 0, v___x_4093_);
lean_ctor_set(v___x_4103_, 1, v___x_4099_);
lean_ctor_set(v___x_4103_, 2, v___x_4101_);
lean_ctor_set(v___x_4103_, 3, v___x_4102_);
v___x_4104_ = l_Lean_Syntax_node1(v___x_4093_, v___x_4098_, v___x_4103_);
v___x_4105_ = l_Lean_Syntax_node2(v___x_4093_, v___x_4095_, v___x_4097_, v___x_4104_);
v___x_4106_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28));
v___x_4107_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4093_);
lean_ctor_set(v___x_4107_, 1, v___x_4106_);
v___x_4108_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4109_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
v___x_4110_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31));
v___x_4111_ = l_Lean_addMacroScope(v_quotContext_4090_, v___x_4110_, v_currMacroScope_4091_);
v___x_4112_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36));
v___x_4113_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4093_);
lean_ctor_set(v___x_4113_, 1, v___x_4109_);
lean_ctor_set(v___x_4113_, 2, v___x_4111_);
lean_ctor_set(v___x_4113_, 3, v___x_4112_);
v___x_4114_ = l_Lean_Syntax_node1(v___x_4093_, v___x_4108_, v___x_4113_);
v___x_4115_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37));
v___x_4116_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4093_);
lean_ctor_set(v___x_4116_, 1, v___x_4115_);
v___x_4117_ = l_Lean_Syntax_node5(v___x_4093_, v___x_4094_, v___x_4105_, v_s_4064_, v___x_4107_, v___x_4114_, v___x_4116_);
v_msg_4068_ = v___x_4117_;
v_quotContext_4069_ = v_quotContext_4090_;
v_currMacroScope_4070_ = v_currMacroScope_4091_;
v_ref_4071_ = v_ref_4092_;
v___y_4072_ = v_a_4066_;
goto v___jp_4067_;
}
else
{
lean_object* v_quotContext_4118_; lean_object* v_currMacroScope_4119_; lean_object* v_ref_4120_; uint8_t v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; 
v_quotContext_4118_ = lean_ctor_get(v_a_4065_, 1);
v_currMacroScope_4119_ = lean_ctor_get(v_a_4065_, 2);
v_ref_4120_ = lean_ctor_get(v_a_4065_, 5);
v___x_4121_ = 0;
v___x_4122_ = l_Lean_SourceInfo_fromRef(v_ref_4120_, v___x_4121_);
v___x_4123_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39));
v___x_4124_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40));
lean_inc(v___x_4122_);
v___x_4125_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4122_);
lean_ctor_set(v___x_4125_, 1, v___x_4124_);
v___x_4126_ = l_Lean_Syntax_node2(v___x_4122_, v___x_4123_, v___x_4125_, v_s_4064_);
lean_inc(v_currMacroScope_4119_);
lean_inc(v_quotContext_4118_);
v_msg_4068_ = v___x_4126_;
v_quotContext_4069_ = v_quotContext_4118_;
v_currMacroScope_4070_ = v_currMacroScope_4119_;
v_ref_4071_ = v_ref_4120_;
v___y_4072_ = v_a_4066_;
goto v___jp_4067_;
}
v___jp_4067_:
{
uint8_t v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4073_ = 0;
v___x_4074_ = l_Lean_SourceInfo_fromRef(v_ref_4071_, v___x_4073_);
v___x_4075_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3));
v___x_4076_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5));
v___x_4077_ = lean_obj_once(&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1, &l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1_once, _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1);
v___x_4078_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3));
v___x_4079_ = l_Lean_addMacroScope(v_quotContext_4069_, v___x_4078_, v_currMacroScope_4070_);
v___x_4080_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6));
lean_inc_n(v___x_4074_, 3);
v___x_4081_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4074_);
lean_ctor_set(v___x_4081_, 1, v___x_4077_);
lean_ctor_set(v___x_4081_, 2, v___x_4079_);
lean_ctor_set(v___x_4081_, 3, v___x_4080_);
v___x_4082_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4083_ = l_Lean_Syntax_node1(v___x_4074_, v___x_4082_, v_msg_4068_);
v___x_4084_ = l_Lean_Syntax_node2(v___x_4074_, v___x_4076_, v___x_4081_, v___x_4083_);
v___x_4085_ = l_Lean_Syntax_node1(v___x_4074_, v___x_4075_, v___x_4084_);
v___x_4086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4085_);
lean_ctor_set(v___x_4086_, 1, v___y_4072_);
return v___x_4086_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___boxed(lean_object* v_s_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_){
_start:
{
lean_object* v_res_4130_; 
v_res_4130_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v_s_4127_, v_a_4128_, v_a_4129_);
lean_dec_ref(v_a_4128_);
return v_res_4130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(lean_object* v_x_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_){
_start:
{
lean_object* v___x_4152_; uint8_t v___x_4153_; 
v___x_4152_ = ((lean_object*)(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1));
lean_inc(v_x_4149_);
v___x_4153_ = l_Lean_Syntax_isOfKind(v_x_4149_, v___x_4152_);
if (v___x_4153_ == 0)
{
lean_object* v___x_4154_; lean_object* v___x_4155_; 
lean_dec(v_x_4149_);
v___x_4154_ = lean_box(1);
v___x_4155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4154_);
lean_ctor_set(v___x_4155_, 1, v_a_4151_);
return v___x_4155_;
}
else
{
lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v_a_4159_; lean_object* v_a_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4167_; 
v___x_4156_ = lean_unsigned_to_nat(1u);
v___x_4157_ = l_Lean_Syntax_getArg(v_x_4149_, v___x_4156_);
lean_dec(v_x_4149_);
v___x_4158_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v___x_4157_, v_a_4150_, v_a_4151_);
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
v_a_4160_ = lean_ctor_get(v___x_4158_, 1);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4162_ = v___x_4158_;
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_inc(v_a_4159_);
lean_dec(v___x_4158_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4165_; 
if (v_isShared_4163_ == 0)
{
v___x_4165_ = v___x_4162_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v_a_4159_);
lean_ctor_set(v_reuseFailAlloc_4166_, 1, v_a_4160_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
return v___x_4165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1___boxed(lean_object* v_x_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(v_x_4168_, v_a_4169_, v_a_4170_);
lean_dec_ref(v_a_4169_);
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg(lean_object* v_a_4172_){
_start:
{
lean_object* v___x_4174_; lean_object* v_issues_4175_; lean_object* v___x_4176_; 
v___x_4174_ = lean_st_ref_get(v_a_4172_);
v_issues_4175_ = lean_ctor_get(v___x_4174_, 8);
lean_inc(v_issues_4175_);
lean_dec(v___x_4174_);
v___x_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4176_, 0, v_issues_4175_);
return v___x_4176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg___boxed(lean_object* v_a_4177_, lean_object* v_a_4178_){
_start:
{
lean_object* v_res_4179_; 
v_res_4179_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4177_);
lean_dec(v_a_4177_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues(lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_){
_start:
{
lean_object* v___x_4187_; 
v___x_4187_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4181_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___boxed(lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l_Lean_Meta_Sym_getIssues(v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_);
lean_dec(v_a_4193_);
lean_dec_ref(v_a_4192_);
lean_dec(v_a_4191_);
lean_dec_ref(v_a_4190_);
lean_dec(v_a_4189_);
lean_dec_ref(v_a_4188_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(lean_object* v_a_4196_, lean_object* v_issues_4197_, lean_object* v_a_x3f_4198_){
_start:
{
lean_object* v___x_4200_; lean_object* v_share_4201_; lean_object* v_maxFVar_4202_; lean_object* v_proofInstInfo_4203_; lean_object* v_inferType_4204_; lean_object* v_getLevel_4205_; lean_object* v_congrInfo_4206_; lean_object* v_defEqI_4207_; lean_object* v_extensions_4208_; lean_object* v_issues_4209_; lean_object* v_canon_4210_; uint8_t v_debug_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4222_; 
v___x_4200_ = lean_st_ref_take(v_a_4196_);
v_share_4201_ = lean_ctor_get(v___x_4200_, 0);
v_maxFVar_4202_ = lean_ctor_get(v___x_4200_, 1);
v_proofInstInfo_4203_ = lean_ctor_get(v___x_4200_, 2);
v_inferType_4204_ = lean_ctor_get(v___x_4200_, 3);
v_getLevel_4205_ = lean_ctor_get(v___x_4200_, 4);
v_congrInfo_4206_ = lean_ctor_get(v___x_4200_, 5);
v_defEqI_4207_ = lean_ctor_get(v___x_4200_, 6);
v_extensions_4208_ = lean_ctor_get(v___x_4200_, 7);
v_issues_4209_ = lean_ctor_get(v___x_4200_, 8);
v_canon_4210_ = lean_ctor_get(v___x_4200_, 9);
v_debug_4211_ = lean_ctor_get_uint8(v___x_4200_, sizeof(void*)*10);
v_isSharedCheck_4222_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4213_ = v___x_4200_;
v_isShared_4214_ = v_isSharedCheck_4222_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_canon_4210_);
lean_inc(v_issues_4209_);
lean_inc(v_extensions_4208_);
lean_inc(v_defEqI_4207_);
lean_inc(v_congrInfo_4206_);
lean_inc(v_getLevel_4205_);
lean_inc(v_inferType_4204_);
lean_inc(v_proofInstInfo_4203_);
lean_inc(v_maxFVar_4202_);
lean_inc(v_share_4201_);
lean_dec(v___x_4200_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4222_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4215_; lean_object* v___x_4217_; 
v___x_4215_ = l_List_appendTR___redArg(v_issues_4209_, v_issues_4197_);
if (v_isShared_4214_ == 0)
{
lean_ctor_set(v___x_4213_, 8, v___x_4215_);
v___x_4217_ = v___x_4213_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v_share_4201_);
lean_ctor_set(v_reuseFailAlloc_4221_, 1, v_maxFVar_4202_);
lean_ctor_set(v_reuseFailAlloc_4221_, 2, v_proofInstInfo_4203_);
lean_ctor_set(v_reuseFailAlloc_4221_, 3, v_inferType_4204_);
lean_ctor_set(v_reuseFailAlloc_4221_, 4, v_getLevel_4205_);
lean_ctor_set(v_reuseFailAlloc_4221_, 5, v_congrInfo_4206_);
lean_ctor_set(v_reuseFailAlloc_4221_, 6, v_defEqI_4207_);
lean_ctor_set(v_reuseFailAlloc_4221_, 7, v_extensions_4208_);
lean_ctor_set(v_reuseFailAlloc_4221_, 8, v___x_4215_);
lean_ctor_set(v_reuseFailAlloc_4221_, 9, v_canon_4210_);
lean_ctor_set_uint8(v_reuseFailAlloc_4221_, sizeof(void*)*10, v_debug_4211_);
v___x_4217_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; 
v___x_4218_ = lean_st_ref_set(v_a_4196_, v___x_4217_);
v___x_4219_ = lean_box(0);
v___x_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4220_, 0, v___x_4219_);
return v___x_4220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0___boxed(lean_object* v_a_4223_, lean_object* v_issues_4224_, lean_object* v_a_x3f_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v_res_4227_; 
v_res_4227_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4223_, v_issues_4224_, v_a_x3f_4225_);
lean_dec(v_a_x3f_4225_);
lean_dec(v_a_4223_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg(lean_object* v_x_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_){
_start:
{
lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v_share_4238_; lean_object* v_maxFVar_4239_; lean_object* v_proofInstInfo_4240_; lean_object* v_inferType_4241_; lean_object* v_getLevel_4242_; lean_object* v_congrInfo_4243_; lean_object* v_defEqI_4244_; lean_object* v_extensions_4245_; lean_object* v_canon_4246_; uint8_t v_debug_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4286_; 
v___x_4236_ = lean_st_ref_get(v_a_4230_);
v___x_4237_ = lean_st_ref_take(v_a_4230_);
v_share_4238_ = lean_ctor_get(v___x_4237_, 0);
v_maxFVar_4239_ = lean_ctor_get(v___x_4237_, 1);
v_proofInstInfo_4240_ = lean_ctor_get(v___x_4237_, 2);
v_inferType_4241_ = lean_ctor_get(v___x_4237_, 3);
v_getLevel_4242_ = lean_ctor_get(v___x_4237_, 4);
v_congrInfo_4243_ = lean_ctor_get(v___x_4237_, 5);
v_defEqI_4244_ = lean_ctor_get(v___x_4237_, 6);
v_extensions_4245_ = lean_ctor_get(v___x_4237_, 7);
v_canon_4246_ = lean_ctor_get(v___x_4237_, 9);
v_debug_4247_ = lean_ctor_get_uint8(v___x_4237_, sizeof(void*)*10);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4286_ == 0)
{
lean_object* v_unused_4287_; 
v_unused_4287_ = lean_ctor_get(v___x_4237_, 8);
lean_dec(v_unused_4287_);
v___x_4249_ = v___x_4237_;
v_isShared_4250_ = v_isSharedCheck_4286_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_canon_4246_);
lean_inc(v_extensions_4245_);
lean_inc(v_defEqI_4244_);
lean_inc(v_congrInfo_4243_);
lean_inc(v_getLevel_4242_);
lean_inc(v_inferType_4241_);
lean_inc(v_proofInstInfo_4240_);
lean_inc(v_maxFVar_4239_);
lean_inc(v_share_4238_);
lean_dec(v___x_4237_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4286_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v___x_4251_; lean_object* v___x_4253_; 
v___x_4251_ = lean_box(0);
if (v_isShared_4250_ == 0)
{
lean_ctor_set(v___x_4249_, 8, v___x_4251_);
v___x_4253_ = v___x_4249_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_share_4238_);
lean_ctor_set(v_reuseFailAlloc_4285_, 1, v_maxFVar_4239_);
lean_ctor_set(v_reuseFailAlloc_4285_, 2, v_proofInstInfo_4240_);
lean_ctor_set(v_reuseFailAlloc_4285_, 3, v_inferType_4241_);
lean_ctor_set(v_reuseFailAlloc_4285_, 4, v_getLevel_4242_);
lean_ctor_set(v_reuseFailAlloc_4285_, 5, v_congrInfo_4243_);
lean_ctor_set(v_reuseFailAlloc_4285_, 6, v_defEqI_4244_);
lean_ctor_set(v_reuseFailAlloc_4285_, 7, v_extensions_4245_);
lean_ctor_set(v_reuseFailAlloc_4285_, 8, v___x_4251_);
lean_ctor_set(v_reuseFailAlloc_4285_, 9, v_canon_4246_);
lean_ctor_set_uint8(v_reuseFailAlloc_4285_, sizeof(void*)*10, v_debug_4247_);
v___x_4253_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
lean_object* v___x_4254_; lean_object* v_issues_4255_; lean_object* v_r_4256_; 
v___x_4254_ = lean_st_ref_set(v_a_4230_, v___x_4253_);
v_issues_4255_ = lean_ctor_get(v___x_4236_, 8);
lean_inc(v_issues_4255_);
lean_dec(v___x_4236_);
lean_inc(v_a_4234_);
lean_inc_ref(v_a_4233_);
lean_inc(v_a_4232_);
lean_inc_ref(v_a_4231_);
lean_inc(v_a_4230_);
lean_inc_ref(v_a_4229_);
v_r_4256_ = lean_apply_7(v_x_4228_, v_a_4229_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_, lean_box(0));
if (lean_obj_tag(v_r_4256_) == 0)
{
lean_object* v_a_4257_; lean_object* v___x_4259_; uint8_t v_isShared_4260_; uint8_t v_isSharedCheck_4273_; 
v_a_4257_ = lean_ctor_get(v_r_4256_, 0);
v_isSharedCheck_4273_ = !lean_is_exclusive(v_r_4256_);
if (v_isSharedCheck_4273_ == 0)
{
v___x_4259_ = v_r_4256_;
v_isShared_4260_ = v_isSharedCheck_4273_;
goto v_resetjp_4258_;
}
else
{
lean_inc(v_a_4257_);
lean_dec(v_r_4256_);
v___x_4259_ = lean_box(0);
v_isShared_4260_ = v_isSharedCheck_4273_;
goto v_resetjp_4258_;
}
v_resetjp_4258_:
{
lean_object* v___x_4262_; 
lean_inc(v_a_4257_);
if (v_isShared_4260_ == 0)
{
lean_ctor_set_tag(v___x_4259_, 1);
v___x_4262_ = v___x_4259_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v_a_4257_);
v___x_4262_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
lean_object* v___x_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4270_; 
v___x_4263_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4230_, v_issues_4255_, v___x_4262_);
lean_dec_ref(v___x_4262_);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4270_ == 0)
{
lean_object* v_unused_4271_; 
v_unused_4271_ = lean_ctor_get(v___x_4263_, 0);
lean_dec(v_unused_4271_);
v___x_4265_ = v___x_4263_;
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
else
{
lean_dec(v___x_4263_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v___x_4268_; 
if (v_isShared_4266_ == 0)
{
lean_ctor_set(v___x_4265_, 0, v_a_4257_);
v___x_4268_ = v___x_4265_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4257_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
}
}
}
else
{
lean_object* v_a_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4283_; 
v_a_4274_ = lean_ctor_get(v_r_4256_, 0);
lean_inc(v_a_4274_);
lean_dec_ref_known(v_r_4256_, 1);
v___x_4275_ = lean_box(0);
v___x_4276_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4230_, v_issues_4255_, v___x_4275_);
v_isSharedCheck_4283_ = !lean_is_exclusive(v___x_4276_);
if (v_isSharedCheck_4283_ == 0)
{
lean_object* v_unused_4284_; 
v_unused_4284_ = lean_ctor_get(v___x_4276_, 0);
lean_dec(v_unused_4284_);
v___x_4278_ = v___x_4276_;
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
else
{
lean_dec(v___x_4276_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v___x_4281_; 
if (v_isShared_4279_ == 0)
{
lean_ctor_set_tag(v___x_4278_, 1);
lean_ctor_set(v___x_4278_, 0, v_a_4274_);
v___x_4281_ = v___x_4278_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_a_4274_);
v___x_4281_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
return v___x_4281_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___boxed(lean_object* v_x_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_){
_start:
{
lean_object* v_res_4296_; 
v_res_4296_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_);
lean_dec(v_a_4294_);
lean_dec_ref(v_a_4293_);
lean_dec(v_a_4292_);
lean_dec_ref(v_a_4291_);
lean_dec(v_a_4290_);
lean_dec_ref(v_a_4289_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext(lean_object* v_00_u03b1_4297_, lean_object* v_x_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_){
_start:
{
lean_object* v___x_4306_; 
v___x_4306_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_4298_, v_a_4299_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_);
return v___x_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___boxed(lean_object* v_00_u03b1_4307_, lean_object* v_x_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_){
_start:
{
lean_object* v_res_4316_; 
v_res_4316_ = l_Lean_Meta_Sym_withNewIssueContext(v_00_u03b1_4307_, v_x_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_);
lean_dec(v_a_4314_);
lean_dec_ref(v_a_4313_);
lean_dec(v_a_4312_);
lean_dec_ref(v_a_4311_);
lean_dec(v_a_4310_);
lean_dec_ref(v_a_4309_);
return v_res_4316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4317_, lean_object* v_vals_4318_, lean_object* v_i_4319_, lean_object* v_k_4320_){
_start:
{
uint8_t v___y_4322_; lean_object* v___x_4328_; uint8_t v___x_4329_; 
v___x_4328_ = lean_array_get_size(v_keys_4317_);
v___x_4329_ = lean_nat_dec_lt(v_i_4319_, v___x_4328_);
if (v___x_4329_ == 0)
{
lean_object* v___x_4330_; 
lean_dec(v_i_4319_);
v___x_4330_ = lean_box(0);
return v___x_4330_;
}
else
{
lean_object* v_fst_4331_; lean_object* v_snd_4332_; lean_object* v_k_x27_4333_; lean_object* v_fst_4334_; lean_object* v_snd_4335_; uint8_t v___x_4336_; 
v_fst_4331_ = lean_ctor_get(v_k_4320_, 0);
v_snd_4332_ = lean_ctor_get(v_k_4320_, 1);
v_k_x27_4333_ = lean_array_fget_borrowed(v_keys_4317_, v_i_4319_);
v_fst_4334_ = lean_ctor_get(v_k_x27_4333_, 0);
v_snd_4335_ = lean_ctor_get(v_k_x27_4333_, 1);
v___x_4336_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_4331_, v_fst_4334_);
if (v___x_4336_ == 0)
{
v___y_4322_ = v___x_4336_;
goto v___jp_4321_;
}
else
{
uint8_t v___x_4337_; 
v___x_4337_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_snd_4332_, v_snd_4335_);
v___y_4322_ = v___x_4337_;
goto v___jp_4321_;
}
}
v___jp_4321_:
{
if (v___y_4322_ == 0)
{
lean_object* v___x_4323_; lean_object* v___x_4324_; 
v___x_4323_ = lean_unsigned_to_nat(1u);
v___x_4324_ = lean_nat_add(v_i_4319_, v___x_4323_);
lean_dec(v_i_4319_);
v_i_4319_ = v___x_4324_;
goto _start;
}
else
{
lean_object* v___x_4326_; lean_object* v___x_4327_; 
v___x_4326_ = lean_array_fget_borrowed(v_vals_4318_, v_i_4319_);
lean_dec(v_i_4319_);
lean_inc(v___x_4326_);
v___x_4327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4327_, 0, v___x_4326_);
return v___x_4327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4338_, lean_object* v_vals_4339_, lean_object* v_i_4340_, lean_object* v_k_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_4338_, v_vals_4339_, v_i_4340_, v_k_4341_);
lean_dec_ref(v_k_4341_);
lean_dec_ref(v_vals_4339_);
lean_dec_ref(v_keys_4338_);
return v_res_4342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(lean_object* v_x_4343_, size_t v_x_4344_, lean_object* v_x_4345_){
_start:
{
if (lean_obj_tag(v_x_4343_) == 0)
{
lean_object* v_es_4346_; lean_object* v___x_4347_; size_t v___x_4348_; size_t v___x_4349_; lean_object* v_j_4350_; lean_object* v___x_4351_; 
v_es_4346_ = lean_ctor_get(v_x_4343_, 0);
v___x_4347_ = lean_box(2);
v___x_4348_ = ((size_t)31ULL);
v___x_4349_ = lean_usize_land(v_x_4344_, v___x_4348_);
v_j_4350_ = lean_usize_to_nat(v___x_4349_);
v___x_4351_ = lean_array_get_borrowed(v___x_4347_, v_es_4346_, v_j_4350_);
lean_dec(v_j_4350_);
switch(lean_obj_tag(v___x_4351_))
{
case 0:
{
lean_object* v_key_4352_; lean_object* v_val_4353_; uint8_t v___y_4355_; lean_object* v_fst_4358_; lean_object* v_snd_4359_; lean_object* v_fst_4360_; lean_object* v_snd_4361_; uint8_t v___x_4362_; 
v_key_4352_ = lean_ctor_get(v___x_4351_, 0);
v_val_4353_ = lean_ctor_get(v___x_4351_, 1);
v_fst_4358_ = lean_ctor_get(v_x_4345_, 0);
v_snd_4359_ = lean_ctor_get(v_x_4345_, 1);
v_fst_4360_ = lean_ctor_get(v_key_4352_, 0);
v_snd_4361_ = lean_ctor_get(v_key_4352_, 1);
v___x_4362_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_4358_, v_fst_4360_);
if (v___x_4362_ == 0)
{
v___y_4355_ = v___x_4362_;
goto v___jp_4354_;
}
else
{
uint8_t v___x_4363_; 
v___x_4363_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_snd_4359_, v_snd_4361_);
v___y_4355_ = v___x_4363_;
goto v___jp_4354_;
}
v___jp_4354_:
{
if (v___y_4355_ == 0)
{
lean_object* v___x_4356_; 
v___x_4356_ = lean_box(0);
return v___x_4356_;
}
else
{
lean_object* v___x_4357_; 
lean_inc(v_val_4353_);
v___x_4357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4357_, 0, v_val_4353_);
return v___x_4357_;
}
}
}
case 1:
{
lean_object* v_node_4364_; size_t v___x_4365_; size_t v___x_4366_; 
v_node_4364_ = lean_ctor_get(v___x_4351_, 0);
v___x_4365_ = ((size_t)5ULL);
v___x_4366_ = lean_usize_shift_right(v_x_4344_, v___x_4365_);
v_x_4343_ = v_node_4364_;
v_x_4344_ = v___x_4366_;
goto _start;
}
default: 
{
lean_object* v___x_4368_; 
v___x_4368_ = lean_box(0);
return v___x_4368_;
}
}
}
else
{
lean_object* v_ks_4369_; lean_object* v_vs_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; 
v_ks_4369_ = lean_ctor_get(v_x_4343_, 0);
v_vs_4370_ = lean_ctor_get(v_x_4343_, 1);
v___x_4371_ = lean_unsigned_to_nat(0u);
v___x_4372_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_ks_4369_, v_vs_4370_, v___x_4371_, v_x_4345_);
return v___x_4372_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg___boxed(lean_object* v_x_4373_, lean_object* v_x_4374_, lean_object* v_x_4375_){
_start:
{
size_t v_x_2646__boxed_4376_; lean_object* v_res_4377_; 
v_x_2646__boxed_4376_ = lean_unbox_usize(v_x_4374_);
lean_dec(v_x_4374_);
v_res_4377_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4373_, v_x_2646__boxed_4376_, v_x_4375_);
lean_dec_ref(v_x_4375_);
lean_dec_ref(v_x_4373_);
return v_res_4377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(lean_object* v_x_4378_, lean_object* v_x_4379_){
_start:
{
lean_object* v_fst_4380_; lean_object* v_snd_4381_; uint64_t v___x_4382_; uint64_t v___x_4383_; uint64_t v___x_4384_; size_t v___x_4385_; lean_object* v___x_4386_; 
v_fst_4380_ = lean_ctor_get(v_x_4379_, 0);
v_snd_4381_ = lean_ctor_get(v_x_4379_, 1);
v___x_4382_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_4380_);
v___x_4383_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_snd_4381_);
v___x_4384_ = lean_uint64_mix_hash(v___x_4382_, v___x_4383_);
v___x_4385_ = lean_uint64_to_usize(v___x_4384_);
v___x_4386_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4378_, v___x_4385_, v_x_4379_);
return v___x_4386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg___boxed(lean_object* v_x_4387_, lean_object* v_x_4388_){
_start:
{
lean_object* v_res_4389_; 
v_res_4389_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_4387_, v_x_4388_);
lean_dec_ref(v_x_4388_);
lean_dec_ref(v_x_4387_);
return v_res_4389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_4390_, lean_object* v_x_4391_, lean_object* v_x_4392_, lean_object* v_x_4393_){
_start:
{
lean_object* v_ks_4394_; lean_object* v_vs_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4424_; 
v_ks_4394_ = lean_ctor_get(v_x_4390_, 0);
v_vs_4395_ = lean_ctor_get(v_x_4390_, 1);
v_isSharedCheck_4424_ = !lean_is_exclusive(v_x_4390_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4397_ = v_x_4390_;
v_isShared_4398_ = v_isSharedCheck_4424_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_vs_4395_);
lean_inc(v_ks_4394_);
lean_dec(v_x_4390_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4424_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
uint8_t v___y_4400_; lean_object* v___x_4412_; uint8_t v___x_4413_; 
v___x_4412_ = lean_array_get_size(v_ks_4394_);
v___x_4413_ = lean_nat_dec_lt(v_x_4391_, v___x_4412_);
if (v___x_4413_ == 0)
{
lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; 
lean_del_object(v___x_4397_);
lean_dec(v_x_4391_);
v___x_4414_ = lean_array_push(v_ks_4394_, v_x_4392_);
v___x_4415_ = lean_array_push(v_vs_4395_, v_x_4393_);
v___x_4416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4416_, 0, v___x_4414_);
lean_ctor_set(v___x_4416_, 1, v___x_4415_);
return v___x_4416_;
}
else
{
lean_object* v_fst_4417_; lean_object* v_snd_4418_; lean_object* v_k_x27_4419_; lean_object* v_fst_4420_; lean_object* v_snd_4421_; uint8_t v___x_4422_; 
v_fst_4417_ = lean_ctor_get(v_x_4392_, 0);
v_snd_4418_ = lean_ctor_get(v_x_4392_, 1);
v_k_x27_4419_ = lean_array_fget_borrowed(v_ks_4394_, v_x_4391_);
v_fst_4420_ = lean_ctor_get(v_k_x27_4419_, 0);
v_snd_4421_ = lean_ctor_get(v_k_x27_4419_, 1);
v___x_4422_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_4417_, v_fst_4420_);
if (v___x_4422_ == 0)
{
v___y_4400_ = v___x_4422_;
goto v___jp_4399_;
}
else
{
uint8_t v___x_4423_; 
v___x_4423_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_snd_4418_, v_snd_4421_);
v___y_4400_ = v___x_4423_;
goto v___jp_4399_;
}
}
v___jp_4399_:
{
if (v___y_4400_ == 0)
{
lean_object* v___x_4402_; 
if (v_isShared_4398_ == 0)
{
v___x_4402_ = v___x_4397_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_ks_4394_);
lean_ctor_set(v_reuseFailAlloc_4406_, 1, v_vs_4395_);
v___x_4402_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4403_ = lean_unsigned_to_nat(1u);
v___x_4404_ = lean_nat_add(v_x_4391_, v___x_4403_);
lean_dec(v_x_4391_);
v_x_4390_ = v___x_4402_;
v_x_4391_ = v___x_4404_;
goto _start;
}
}
else
{
lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4410_; 
v___x_4407_ = lean_array_fset(v_ks_4394_, v_x_4391_, v_x_4392_);
v___x_4408_ = lean_array_fset(v_vs_4395_, v_x_4391_, v_x_4393_);
lean_dec(v_x_4391_);
if (v_isShared_4398_ == 0)
{
lean_ctor_set(v___x_4397_, 1, v___x_4408_);
lean_ctor_set(v___x_4397_, 0, v___x_4407_);
v___x_4410_ = v___x_4397_;
goto v_reusejp_4409_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v___x_4407_);
lean_ctor_set(v_reuseFailAlloc_4411_, 1, v___x_4408_);
v___x_4410_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4409_;
}
v_reusejp_4409_:
{
return v___x_4410_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(lean_object* v_n_4425_, lean_object* v_k_4426_, lean_object* v_v_4427_){
_start:
{
lean_object* v___x_4428_; lean_object* v___x_4429_; 
v___x_4428_ = lean_unsigned_to_nat(0u);
v___x_4429_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_n_4425_, v___x_4428_, v_k_4426_, v_v_4427_);
return v___x_4429_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4430_; 
v___x_4430_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(lean_object* v_x_4431_, size_t v_x_4432_, size_t v_x_4433_, lean_object* v_x_4434_, lean_object* v_x_4435_){
_start:
{
if (lean_obj_tag(v_x_4431_) == 0)
{
lean_object* v_es_4436_; size_t v___x_4437_; size_t v___x_4438_; lean_object* v_j_4439_; lean_object* v___x_4440_; uint8_t v___x_4441_; 
v_es_4436_ = lean_ctor_get(v_x_4431_, 0);
v___x_4437_ = ((size_t)31ULL);
v___x_4438_ = lean_usize_land(v_x_4432_, v___x_4437_);
v_j_4439_ = lean_usize_to_nat(v___x_4438_);
v___x_4440_ = lean_array_get_size(v_es_4436_);
v___x_4441_ = lean_nat_dec_lt(v_j_4439_, v___x_4440_);
if (v___x_4441_ == 0)
{
lean_dec(v_j_4439_);
lean_dec(v_x_4435_);
lean_dec_ref(v_x_4434_);
return v_x_4431_;
}
else
{
lean_object* v___x_4443_; uint8_t v_isShared_4444_; uint8_t v_isSharedCheck_4487_; 
lean_inc_ref(v_es_4436_);
v_isSharedCheck_4487_ = !lean_is_exclusive(v_x_4431_);
if (v_isSharedCheck_4487_ == 0)
{
lean_object* v_unused_4488_; 
v_unused_4488_ = lean_ctor_get(v_x_4431_, 0);
lean_dec(v_unused_4488_);
v___x_4443_ = v_x_4431_;
v_isShared_4444_ = v_isSharedCheck_4487_;
goto v_resetjp_4442_;
}
else
{
lean_dec(v_x_4431_);
v___x_4443_ = lean_box(0);
v_isShared_4444_ = v_isSharedCheck_4487_;
goto v_resetjp_4442_;
}
v_resetjp_4442_:
{
lean_object* v_v_4445_; lean_object* v___x_4446_; lean_object* v_xs_x27_4447_; lean_object* v___y_4449_; 
v_v_4445_ = lean_array_fget(v_es_4436_, v_j_4439_);
v___x_4446_ = lean_box(0);
v_xs_x27_4447_ = lean_array_fset(v_es_4436_, v_j_4439_, v___x_4446_);
switch(lean_obj_tag(v_v_4445_))
{
case 0:
{
lean_object* v_key_4454_; lean_object* v_val_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4472_; 
v_key_4454_ = lean_ctor_get(v_v_4445_, 0);
v_val_4455_ = lean_ctor_get(v_v_4445_, 1);
v_isSharedCheck_4472_ = !lean_is_exclusive(v_v_4445_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4457_ = v_v_4445_;
v_isShared_4458_ = v_isSharedCheck_4472_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_val_4455_);
lean_inc(v_key_4454_);
lean_dec(v_v_4445_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4472_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
uint8_t v___y_4460_; lean_object* v_fst_4466_; lean_object* v_snd_4467_; lean_object* v_fst_4468_; lean_object* v_snd_4469_; uint8_t v___x_4470_; 
v_fst_4466_ = lean_ctor_get(v_x_4434_, 0);
v_snd_4467_ = lean_ctor_get(v_x_4434_, 1);
v_fst_4468_ = lean_ctor_get(v_key_4454_, 0);
v_snd_4469_ = lean_ctor_get(v_key_4454_, 1);
v___x_4470_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_4466_, v_fst_4468_);
if (v___x_4470_ == 0)
{
v___y_4460_ = v___x_4470_;
goto v___jp_4459_;
}
else
{
uint8_t v___x_4471_; 
v___x_4471_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_snd_4467_, v_snd_4469_);
v___y_4460_ = v___x_4471_;
goto v___jp_4459_;
}
v___jp_4459_:
{
if (v___y_4460_ == 0)
{
lean_object* v___x_4461_; lean_object* v___x_4462_; 
lean_del_object(v___x_4457_);
v___x_4461_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4454_, v_val_4455_, v_x_4434_, v_x_4435_);
v___x_4462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4462_, 0, v___x_4461_);
v___y_4449_ = v___x_4462_;
goto v___jp_4448_;
}
else
{
lean_object* v___x_4464_; 
lean_dec(v_val_4455_);
lean_dec(v_key_4454_);
if (v_isShared_4458_ == 0)
{
lean_ctor_set(v___x_4457_, 1, v_x_4435_);
lean_ctor_set(v___x_4457_, 0, v_x_4434_);
v___x_4464_ = v___x_4457_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_x_4434_);
lean_ctor_set(v_reuseFailAlloc_4465_, 1, v_x_4435_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
v___y_4449_ = v___x_4464_;
goto v___jp_4448_;
}
}
}
}
}
case 1:
{
lean_object* v_node_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4485_; 
v_node_4473_ = lean_ctor_get(v_v_4445_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v_v_4445_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4475_ = v_v_4445_;
v_isShared_4476_ = v_isSharedCheck_4485_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_node_4473_);
lean_dec(v_v_4445_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4485_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
size_t v___x_4477_; size_t v___x_4478_; size_t v___x_4479_; size_t v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4483_; 
v___x_4477_ = ((size_t)5ULL);
v___x_4478_ = lean_usize_shift_right(v_x_4432_, v___x_4477_);
v___x_4479_ = ((size_t)1ULL);
v___x_4480_ = lean_usize_add(v_x_4433_, v___x_4479_);
v___x_4481_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_node_4473_, v___x_4478_, v___x_4480_, v_x_4434_, v_x_4435_);
if (v_isShared_4476_ == 0)
{
lean_ctor_set(v___x_4475_, 0, v___x_4481_);
v___x_4483_ = v___x_4475_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v___x_4481_);
v___x_4483_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
v___y_4449_ = v___x_4483_;
goto v___jp_4448_;
}
}
}
default: 
{
lean_object* v___x_4486_; 
v___x_4486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4486_, 0, v_x_4434_);
lean_ctor_set(v___x_4486_, 1, v_x_4435_);
v___y_4449_ = v___x_4486_;
goto v___jp_4448_;
}
}
v___jp_4448_:
{
lean_object* v___x_4450_; lean_object* v___x_4452_; 
v___x_4450_ = lean_array_fset(v_xs_x27_4447_, v_j_4439_, v___y_4449_);
lean_dec(v_j_4439_);
if (v_isShared_4444_ == 0)
{
lean_ctor_set(v___x_4443_, 0, v___x_4450_);
v___x_4452_ = v___x_4443_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v___x_4450_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
}
}
else
{
lean_object* v_ks_4489_; lean_object* v_vs_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4510_; 
v_ks_4489_ = lean_ctor_get(v_x_4431_, 0);
v_vs_4490_ = lean_ctor_get(v_x_4431_, 1);
v_isSharedCheck_4510_ = !lean_is_exclusive(v_x_4431_);
if (v_isSharedCheck_4510_ == 0)
{
v___x_4492_ = v_x_4431_;
v_isShared_4493_ = v_isSharedCheck_4510_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_vs_4490_);
lean_inc(v_ks_4489_);
lean_dec(v_x_4431_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4510_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4495_; 
if (v_isShared_4493_ == 0)
{
v___x_4495_ = v___x_4492_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_ks_4489_);
lean_ctor_set(v_reuseFailAlloc_4509_, 1, v_vs_4490_);
v___x_4495_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
lean_object* v_newNode_4496_; uint8_t v___y_4498_; size_t v___x_4504_; uint8_t v___x_4505_; 
v_newNode_4496_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v___x_4495_, v_x_4434_, v_x_4435_);
v___x_4504_ = ((size_t)7ULL);
v___x_4505_ = lean_usize_dec_le(v___x_4504_, v_x_4433_);
if (v___x_4505_ == 0)
{
lean_object* v___x_4506_; lean_object* v___x_4507_; uint8_t v___x_4508_; 
v___x_4506_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4496_);
v___x_4507_ = lean_unsigned_to_nat(4u);
v___x_4508_ = lean_nat_dec_lt(v___x_4506_, v___x_4507_);
lean_dec(v___x_4506_);
v___y_4498_ = v___x_4508_;
goto v___jp_4497_;
}
else
{
v___y_4498_ = v___x_4505_;
goto v___jp_4497_;
}
v___jp_4497_:
{
if (v___y_4498_ == 0)
{
lean_object* v_ks_4499_; lean_object* v_vs_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; 
v_ks_4499_ = lean_ctor_get(v_newNode_4496_, 0);
lean_inc_ref(v_ks_4499_);
v_vs_4500_ = lean_ctor_get(v_newNode_4496_, 1);
lean_inc_ref(v_vs_4500_);
lean_dec_ref(v_newNode_4496_);
v___x_4501_ = lean_unsigned_to_nat(0u);
v___x_4502_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0);
v___x_4503_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_x_4433_, v_ks_4499_, v_vs_4500_, v___x_4501_, v___x_4502_);
lean_dec_ref(v_vs_4500_);
lean_dec_ref(v_ks_4499_);
return v___x_4503_;
}
else
{
return v_newNode_4496_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(size_t v_depth_4511_, lean_object* v_keys_4512_, lean_object* v_vals_4513_, lean_object* v_i_4514_, lean_object* v_entries_4515_){
_start:
{
lean_object* v___x_4516_; uint8_t v___x_4517_; 
v___x_4516_ = lean_array_get_size(v_keys_4512_);
v___x_4517_ = lean_nat_dec_lt(v_i_4514_, v___x_4516_);
if (v___x_4517_ == 0)
{
lean_dec(v_i_4514_);
return v_entries_4515_;
}
else
{
lean_object* v_k_4518_; lean_object* v_fst_4519_; lean_object* v_snd_4520_; lean_object* v_v_4521_; uint64_t v___x_4522_; uint64_t v___x_4523_; uint64_t v___x_4524_; size_t v_h_4525_; size_t v___x_4526_; lean_object* v___x_4527_; size_t v___x_4528_; size_t v___x_4529_; size_t v___x_4530_; size_t v_h_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; 
v_k_4518_ = lean_array_fget_borrowed(v_keys_4512_, v_i_4514_);
v_fst_4519_ = lean_ctor_get(v_k_4518_, 0);
v_snd_4520_ = lean_ctor_get(v_k_4518_, 1);
v_v_4521_ = lean_array_fget_borrowed(v_vals_4513_, v_i_4514_);
v___x_4522_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_4519_);
v___x_4523_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_snd_4520_);
v___x_4524_ = lean_uint64_mix_hash(v___x_4522_, v___x_4523_);
v_h_4525_ = lean_uint64_to_usize(v___x_4524_);
v___x_4526_ = ((size_t)5ULL);
v___x_4527_ = lean_unsigned_to_nat(1u);
v___x_4528_ = ((size_t)1ULL);
v___x_4529_ = lean_usize_sub(v_depth_4511_, v___x_4528_);
v___x_4530_ = lean_usize_mul(v___x_4526_, v___x_4529_);
v_h_4531_ = lean_usize_shift_right(v_h_4525_, v___x_4530_);
v___x_4532_ = lean_nat_add(v_i_4514_, v___x_4527_);
lean_dec(v_i_4514_);
lean_inc(v_v_4521_);
lean_inc(v_k_4518_);
v___x_4533_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_entries_4515_, v_h_4531_, v_depth_4511_, v_k_4518_, v_v_4521_);
v_i_4514_ = v___x_4532_;
v_entries_4515_ = v___x_4533_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_4535_, lean_object* v_keys_4536_, lean_object* v_vals_4537_, lean_object* v_i_4538_, lean_object* v_entries_4539_){
_start:
{
size_t v_depth_boxed_4540_; lean_object* v_res_4541_; 
v_depth_boxed_4540_ = lean_unbox_usize(v_depth_4535_);
lean_dec(v_depth_4535_);
v_res_4541_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_boxed_4540_, v_keys_4536_, v_vals_4537_, v_i_4538_, v_entries_4539_);
lean_dec_ref(v_vals_4537_);
lean_dec_ref(v_keys_4536_);
return v_res_4541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___boxed(lean_object* v_x_4542_, lean_object* v_x_4543_, lean_object* v_x_4544_, lean_object* v_x_4545_, lean_object* v_x_4546_){
_start:
{
size_t v_x_2817__boxed_4547_; size_t v_x_2818__boxed_4548_; lean_object* v_res_4549_; 
v_x_2817__boxed_4547_ = lean_unbox_usize(v_x_4543_);
lean_dec(v_x_4543_);
v_x_2818__boxed_4548_ = lean_unbox_usize(v_x_4544_);
lean_dec(v_x_4544_);
v_res_4549_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4542_, v_x_2817__boxed_4547_, v_x_2818__boxed_4548_, v_x_4545_, v_x_4546_);
return v_res_4549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(lean_object* v_x_4550_, lean_object* v_x_4551_, lean_object* v_x_4552_){
_start:
{
lean_object* v_fst_4553_; lean_object* v_snd_4554_; uint64_t v___x_4555_; uint64_t v___x_4556_; uint64_t v___x_4557_; size_t v___x_4558_; size_t v___x_4559_; lean_object* v___x_4560_; 
v_fst_4553_ = lean_ctor_get(v_x_4551_, 0);
v_snd_4554_ = lean_ctor_get(v_x_4551_, 1);
v___x_4555_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_4553_);
v___x_4556_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_snd_4554_);
v___x_4557_ = lean_uint64_mix_hash(v___x_4555_, v___x_4556_);
v___x_4558_ = lean_uint64_to_usize(v___x_4557_);
v___x_4559_ = ((size_t)1ULL);
v___x_4560_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4550_, v___x_4558_, v___x_4559_, v_x_4551_, v_x_4552_);
return v___x_4560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object* v_s_4561_, lean_object* v_t_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_){
_start:
{
lean_object* v___x_4569_; lean_object* v_defEqI_4570_; lean_object* v_key_4571_; lean_object* v___x_4572_; 
v___x_4569_ = lean_st_ref_get(v_a_4563_);
v_defEqI_4570_ = lean_ctor_get(v___x_4569_, 6);
lean_inc_ref(v_defEqI_4570_);
lean_dec(v___x_4569_);
lean_inc_ref(v_t_4562_);
lean_inc_ref(v_s_4561_);
v_key_4571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_4571_, 0, v_s_4561_);
lean_ctor_set(v_key_4571_, 1, v_t_4562_);
v___x_4572_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_defEqI_4570_, v_key_4571_);
lean_dec_ref(v_defEqI_4570_);
if (lean_obj_tag(v___x_4572_) == 1)
{
lean_object* v_val_4573_; lean_object* v___x_4575_; uint8_t v_isShared_4576_; uint8_t v_isSharedCheck_4580_; 
lean_dec_ref_known(v_key_4571_, 2);
lean_dec_ref(v_t_4562_);
lean_dec_ref(v_s_4561_);
v_val_4573_ = lean_ctor_get(v___x_4572_, 0);
v_isSharedCheck_4580_ = !lean_is_exclusive(v___x_4572_);
if (v_isSharedCheck_4580_ == 0)
{
v___x_4575_ = v___x_4572_;
v_isShared_4576_ = v_isSharedCheck_4580_;
goto v_resetjp_4574_;
}
else
{
lean_inc(v_val_4573_);
lean_dec(v___x_4572_);
v___x_4575_ = lean_box(0);
v_isShared_4576_ = v_isSharedCheck_4580_;
goto v_resetjp_4574_;
}
v_resetjp_4574_:
{
lean_object* v___x_4578_; 
if (v_isShared_4576_ == 0)
{
lean_ctor_set_tag(v___x_4575_, 0);
v___x_4578_ = v___x_4575_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4579_; 
v_reuseFailAlloc_4579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4579_, 0, v_val_4573_);
v___x_4578_ = v_reuseFailAlloc_4579_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
return v___x_4578_;
}
}
}
else
{
lean_object* v___x_4581_; 
lean_dec(v___x_4572_);
v___x_4581_ = l_Lean_Meta_isDefEqI(v_s_4561_, v_t_4562_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_);
if (lean_obj_tag(v___x_4581_) == 0)
{
lean_object* v_a_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4610_; 
v_a_4582_ = lean_ctor_get(v___x_4581_, 0);
v_isSharedCheck_4610_ = !lean_is_exclusive(v___x_4581_);
if (v_isSharedCheck_4610_ == 0)
{
v___x_4584_ = v___x_4581_;
v_isShared_4585_ = v_isSharedCheck_4610_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_a_4582_);
lean_dec(v___x_4581_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4610_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
lean_object* v___x_4586_; lean_object* v_share_4587_; lean_object* v_maxFVar_4588_; lean_object* v_proofInstInfo_4589_; lean_object* v_inferType_4590_; lean_object* v_getLevel_4591_; lean_object* v_congrInfo_4592_; lean_object* v_defEqI_4593_; lean_object* v_extensions_4594_; lean_object* v_issues_4595_; lean_object* v_canon_4596_; uint8_t v_debug_4597_; lean_object* v___x_4599_; uint8_t v_isShared_4600_; uint8_t v_isSharedCheck_4609_; 
v___x_4586_ = lean_st_ref_take(v_a_4563_);
v_share_4587_ = lean_ctor_get(v___x_4586_, 0);
v_maxFVar_4588_ = lean_ctor_get(v___x_4586_, 1);
v_proofInstInfo_4589_ = lean_ctor_get(v___x_4586_, 2);
v_inferType_4590_ = lean_ctor_get(v___x_4586_, 3);
v_getLevel_4591_ = lean_ctor_get(v___x_4586_, 4);
v_congrInfo_4592_ = lean_ctor_get(v___x_4586_, 5);
v_defEqI_4593_ = lean_ctor_get(v___x_4586_, 6);
v_extensions_4594_ = lean_ctor_get(v___x_4586_, 7);
v_issues_4595_ = lean_ctor_get(v___x_4586_, 8);
v_canon_4596_ = lean_ctor_get(v___x_4586_, 9);
v_debug_4597_ = lean_ctor_get_uint8(v___x_4586_, sizeof(void*)*10);
v_isSharedCheck_4609_ = !lean_is_exclusive(v___x_4586_);
if (v_isSharedCheck_4609_ == 0)
{
v___x_4599_ = v___x_4586_;
v_isShared_4600_ = v_isSharedCheck_4609_;
goto v_resetjp_4598_;
}
else
{
lean_inc(v_canon_4596_);
lean_inc(v_issues_4595_);
lean_inc(v_extensions_4594_);
lean_inc(v_defEqI_4593_);
lean_inc(v_congrInfo_4592_);
lean_inc(v_getLevel_4591_);
lean_inc(v_inferType_4590_);
lean_inc(v_proofInstInfo_4589_);
lean_inc(v_maxFVar_4588_);
lean_inc(v_share_4587_);
lean_dec(v___x_4586_);
v___x_4599_ = lean_box(0);
v_isShared_4600_ = v_isSharedCheck_4609_;
goto v_resetjp_4598_;
}
v_resetjp_4598_:
{
lean_object* v___x_4601_; lean_object* v___x_4603_; 
lean_inc(v_a_4582_);
v___x_4601_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_defEqI_4593_, v_key_4571_, v_a_4582_);
if (v_isShared_4600_ == 0)
{
lean_ctor_set(v___x_4599_, 6, v___x_4601_);
v___x_4603_ = v___x_4599_;
goto v_reusejp_4602_;
}
else
{
lean_object* v_reuseFailAlloc_4608_; 
v_reuseFailAlloc_4608_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_4608_, 0, v_share_4587_);
lean_ctor_set(v_reuseFailAlloc_4608_, 1, v_maxFVar_4588_);
lean_ctor_set(v_reuseFailAlloc_4608_, 2, v_proofInstInfo_4589_);
lean_ctor_set(v_reuseFailAlloc_4608_, 3, v_inferType_4590_);
lean_ctor_set(v_reuseFailAlloc_4608_, 4, v_getLevel_4591_);
lean_ctor_set(v_reuseFailAlloc_4608_, 5, v_congrInfo_4592_);
lean_ctor_set(v_reuseFailAlloc_4608_, 6, v___x_4601_);
lean_ctor_set(v_reuseFailAlloc_4608_, 7, v_extensions_4594_);
lean_ctor_set(v_reuseFailAlloc_4608_, 8, v_issues_4595_);
lean_ctor_set(v_reuseFailAlloc_4608_, 9, v_canon_4596_);
lean_ctor_set_uint8(v_reuseFailAlloc_4608_, sizeof(void*)*10, v_debug_4597_);
v___x_4603_ = v_reuseFailAlloc_4608_;
goto v_reusejp_4602_;
}
v_reusejp_4602_:
{
lean_object* v___x_4604_; lean_object* v___x_4606_; 
v___x_4604_ = lean_st_ref_set(v_a_4563_, v___x_4603_);
if (v_isShared_4585_ == 0)
{
v___x_4606_ = v___x_4584_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_a_4582_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
return v___x_4606_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_4571_, 2);
return v___x_4581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg___boxed(lean_object* v_s_4611_, lean_object* v_t_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_){
_start:
{
lean_object* v_res_4619_; 
v_res_4619_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_4611_, v_t_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_);
lean_dec(v_a_4617_);
lean_dec_ref(v_a_4616_);
lean_dec(v_a_4615_);
lean_dec_ref(v_a_4614_);
lean_dec(v_a_4613_);
return v_res_4619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI(lean_object* v_s_4620_, lean_object* v_t_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_){
_start:
{
lean_object* v___x_4629_; 
v___x_4629_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_4620_, v_t_4621_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_, v_a_4627_);
return v___x_4629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___boxed(lean_object* v_s_4630_, lean_object* v_t_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_){
_start:
{
lean_object* v_res_4639_; 
v_res_4639_ = l_Lean_Meta_Sym_isDefEqI(v_s_4630_, v_t_4631_, v_a_4632_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_);
lean_dec(v_a_4637_);
lean_dec_ref(v_a_4636_);
lean_dec(v_a_4635_);
lean_dec_ref(v_a_4634_);
lean_dec(v_a_4633_);
lean_dec_ref(v_a_4632_);
return v_res_4639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(lean_object* v_00_u03b2_4640_, lean_object* v_x_4641_, lean_object* v_x_4642_){
_start:
{
lean_object* v___x_4643_; 
v___x_4643_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_4641_, v_x_4642_);
return v___x_4643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___boxed(lean_object* v_00_u03b2_4644_, lean_object* v_x_4645_, lean_object* v_x_4646_){
_start:
{
lean_object* v_res_4647_; 
v_res_4647_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(v_00_u03b2_4644_, v_x_4645_, v_x_4646_);
lean_dec_ref(v_x_4646_);
lean_dec_ref(v_x_4645_);
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1(lean_object* v_00_u03b2_4648_, lean_object* v_x_4649_, lean_object* v_x_4650_, lean_object* v_x_4651_){
_start:
{
lean_object* v___x_4652_; 
v___x_4652_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_x_4649_, v_x_4650_, v_x_4651_);
return v___x_4652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(lean_object* v_00_u03b2_4653_, lean_object* v_x_4654_, size_t v_x_4655_, lean_object* v_x_4656_){
_start:
{
lean_object* v___x_4657_; 
v___x_4657_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4654_, v_x_4655_, v_x_4656_);
return v___x_4657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4658_, lean_object* v_x_4659_, lean_object* v_x_4660_, lean_object* v_x_4661_){
_start:
{
size_t v_x_3096__boxed_4662_; lean_object* v_res_4663_; 
v_x_3096__boxed_4662_ = lean_unbox_usize(v_x_4660_);
lean_dec(v_x_4660_);
v_res_4663_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(v_00_u03b2_4658_, v_x_4659_, v_x_3096__boxed_4662_, v_x_4661_);
lean_dec_ref(v_x_4661_);
lean_dec_ref(v_x_4659_);
return v_res_4663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(lean_object* v_00_u03b2_4664_, lean_object* v_x_4665_, size_t v_x_4666_, size_t v_x_4667_, lean_object* v_x_4668_, lean_object* v_x_4669_){
_start:
{
lean_object* v___x_4670_; 
v___x_4670_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4665_, v_x_4666_, v_x_4667_, v_x_4668_, v_x_4669_);
return v___x_4670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4671_, lean_object* v_x_4672_, lean_object* v_x_4673_, lean_object* v_x_4674_, lean_object* v_x_4675_, lean_object* v_x_4676_){
_start:
{
size_t v_x_3107__boxed_4677_; size_t v_x_3108__boxed_4678_; lean_object* v_res_4679_; 
v_x_3107__boxed_4677_ = lean_unbox_usize(v_x_4673_);
lean_dec(v_x_4673_);
v_x_3108__boxed_4678_ = lean_unbox_usize(v_x_4674_);
lean_dec(v_x_4674_);
v_res_4679_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(v_00_u03b2_4671_, v_x_4672_, v_x_3107__boxed_4677_, v_x_3108__boxed_4678_, v_x_4675_, v_x_4676_);
return v_res_4679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4680_, lean_object* v_keys_4681_, lean_object* v_vals_4682_, lean_object* v_heq_4683_, lean_object* v_i_4684_, lean_object* v_k_4685_){
_start:
{
lean_object* v___x_4686_; 
v___x_4686_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_4681_, v_vals_4682_, v_i_4684_, v_k_4685_);
return v___x_4686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4687_, lean_object* v_keys_4688_, lean_object* v_vals_4689_, lean_object* v_heq_4690_, lean_object* v_i_4691_, lean_object* v_k_4692_){
_start:
{
lean_object* v_res_4693_; 
v_res_4693_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(v_00_u03b2_4687_, v_keys_4688_, v_vals_4689_, v_heq_4690_, v_i_4691_, v_k_4692_);
lean_dec_ref(v_k_4692_);
lean_dec_ref(v_vals_4689_);
lean_dec_ref(v_keys_4688_);
return v_res_4693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4694_, lean_object* v_n_4695_, lean_object* v_k_4696_, lean_object* v_v_4697_){
_start:
{
lean_object* v___x_4698_; 
v___x_4698_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v_n_4695_, v_k_4696_, v_v_4697_);
return v___x_4698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_4699_, size_t v_depth_4700_, lean_object* v_keys_4701_, lean_object* v_vals_4702_, lean_object* v_heq_4703_, lean_object* v_i_4704_, lean_object* v_entries_4705_){
_start:
{
lean_object* v___x_4706_; 
v___x_4706_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_4700_, v_keys_4701_, v_vals_4702_, v_i_4704_, v_entries_4705_);
return v___x_4706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_4707_, lean_object* v_depth_4708_, lean_object* v_keys_4709_, lean_object* v_vals_4710_, lean_object* v_heq_4711_, lean_object* v_i_4712_, lean_object* v_entries_4713_){
_start:
{
size_t v_depth_boxed_4714_; lean_object* v_res_4715_; 
v_depth_boxed_4714_ = lean_unbox_usize(v_depth_4708_);
lean_dec(v_depth_4708_);
v_res_4715_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(v_00_u03b2_4707_, v_depth_boxed_4714_, v_keys_4709_, v_vals_4710_, v_heq_4711_, v_i_4712_, v_entries_4713_);
lean_dec_ref(v_vals_4710_);
lean_dec_ref(v_keys_4709_);
return v_res_4715_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_4716_, lean_object* v_x_4717_, lean_object* v_x_4718_, lean_object* v_x_4719_, lean_object* v_x_4720_){
_start:
{
lean_object* v___x_4721_; 
v___x_4721_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_x_4717_, v_x_4718_, v_x_4719_, v_x_4720_);
return v___x_4721_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0(void){
_start:
{
lean_object* v___x_4722_; lean_object* v___f_4723_; 
v___x_4722_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_4723_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4723_, 0, v___x_4722_);
return v___f_4723_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__1(void){
_start:
{
lean_object* v___x_4724_; lean_object* v___f_4725_; 
v___x_4724_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_4725_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4725_, 0, v___x_4724_);
return v___f_4725_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__2(void){
_start:
{
lean_object* v___f_4726_; lean_object* v___f_4727_; lean_object* v___x_4728_; 
v___f_4726_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__1, &l_Lean_Meta_Sym_instInhabitedSymM___closed__1_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__1);
v___f_4727_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__0, &l_Lean_Meta_Sym_instInhabitedSymM___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0);
v___x_4728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4728_, 0, v___f_4727_);
lean_ctor_set(v___x_4728_, 1, v___f_4726_);
return v___x_4728_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__3(void){
_start:
{
lean_object* v___x_4729_; lean_object* v___f_4730_; 
v___x_4729_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__2, &l_Lean_Meta_Sym_instInhabitedSymM___closed__2_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__2);
v___f_4730_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4730_, 0, v___x_4729_);
return v___f_4730_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__4(void){
_start:
{
lean_object* v___x_4731_; lean_object* v___f_4732_; 
v___x_4731_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__2, &l_Lean_Meta_Sym_instInhabitedSymM___closed__2_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__2);
v___f_4732_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4732_, 0, v___x_4731_);
return v___f_4732_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__5(void){
_start:
{
lean_object* v___f_4733_; lean_object* v___f_4734_; lean_object* v___x_4735_; 
v___f_4733_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__4, &l_Lean_Meta_Sym_instInhabitedSymM___closed__4_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__4);
v___f_4734_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__3, &l_Lean_Meta_Sym_instInhabitedSymM___closed__3_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__3);
v___x_4735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4735_, 0, v___f_4734_);
lean_ctor_set(v___x_4735_, 1, v___f_4733_);
return v___x_4735_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__6(void){
_start:
{
lean_object* v___x_4736_; lean_object* v___f_4737_; 
v___x_4736_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__5, &l_Lean_Meta_Sym_instInhabitedSymM___closed__5_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__5);
v___f_4737_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4737_, 0, v___x_4736_);
return v___f_4737_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__7(void){
_start:
{
lean_object* v___x_4738_; lean_object* v___f_4739_; 
v___x_4738_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__5, &l_Lean_Meta_Sym_instInhabitedSymM___closed__5_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__5);
v___f_4739_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4739_, 0, v___x_4738_);
return v___f_4739_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8(void){
_start:
{
lean_object* v___f_4740_; lean_object* v___f_4741_; lean_object* v___x_4742_; 
v___f_4740_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__7, &l_Lean_Meta_Sym_instInhabitedSymM___closed__7_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__7);
v___f_4741_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__6, &l_Lean_Meta_Sym_instInhabitedSymM___closed__6_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__6);
v___x_4742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4742_, 0, v___f_4741_);
lean_ctor_set(v___x_4742_, 1, v___f_4740_);
return v___x_4742_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__9(void){
_start:
{
lean_object* v___x_4743_; lean_object* v___f_4744_; 
v___x_4743_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__8, &l_Lean_Meta_Sym_instInhabitedSymM___closed__8_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8);
v___f_4744_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4744_, 0, v___x_4743_);
return v___f_4744_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__10(void){
_start:
{
lean_object* v___x_4745_; lean_object* v___f_4746_; 
v___x_4745_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__8, &l_Lean_Meta_Sym_instInhabitedSymM___closed__8_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8);
v___f_4746_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4746_, 0, v___x_4745_);
return v___f_4746_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__11(void){
_start:
{
lean_object* v___f_4747_; lean_object* v___f_4748_; lean_object* v___x_4749_; 
v___f_4747_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__10, &l_Lean_Meta_Sym_instInhabitedSymM___closed__10_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__10);
v___f_4748_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__9, &l_Lean_Meta_Sym_instInhabitedSymM___closed__9_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__9);
v___x_4749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4749_, 0, v___f_4748_);
lean_ctor_set(v___x_4749_, 1, v___f_4747_);
return v___x_4749_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__16(void){
_start:
{
lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; 
v___x_4754_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_4755_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__15));
v___x_4756_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__14));
v___x_4757_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_4756_, v___x_4755_, v___x_4754_);
return v___x_4757_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__17(void){
_start:
{
lean_object* v___x_4758_; lean_object* v___f_4759_; lean_object* v___f_4760_; lean_object* v___x_4761_; 
v___x_4758_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__16, &l_Lean_Meta_Sym_instInhabitedSymM___closed__16_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__16);
v___f_4759_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__13));
v___f_4760_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__12));
v___x_4761_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_4760_, v___f_4759_, v___x_4758_);
return v___x_4761_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__18(void){
_start:
{
lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; 
v___x_4762_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__17, &l_Lean_Meta_Sym_instInhabitedSymM___closed__17_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__17);
v___x_4763_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__15));
v___x_4764_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__14));
v___x_4765_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_4764_, v___x_4763_, v___x_4762_);
return v___x_4765_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__19(void){
_start:
{
lean_object* v___x_4766_; lean_object* v___f_4767_; lean_object* v___f_4768_; lean_object* v___x_4769_; 
v___x_4766_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__18, &l_Lean_Meta_Sym_instInhabitedSymM___closed__18_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__18);
v___f_4767_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__13));
v___f_4768_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__12));
v___x_4769_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_4768_, v___f_4767_, v___x_4766_);
return v___x_4769_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__20(void){
_start:
{
lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___f_4772_; 
v___x_4770_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__15));
v___x_4771_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_4772_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4772_, 0, v___x_4771_);
lean_closure_set(v___f_4772_, 1, v___x_4770_);
return v___f_4772_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__21(void){
_start:
{
lean_object* v___f_4773_; lean_object* v___f_4774_; lean_object* v___f_4775_; 
v___f_4773_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__13));
v___f_4774_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__20, &l_Lean_Meta_Sym_instInhabitedSymM___closed__20_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__20);
v___f_4775_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4775_, 0, v___f_4774_);
lean_closure_set(v___f_4775_, 1, v___f_4773_);
return v___f_4775_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__23(void){
_start:
{
lean_object* v___x_4777_; lean_object* v___x_4778_; 
v___x_4777_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__22));
v___x_4778_ = l_Lean_stringToMessageData(v___x_4777_);
return v___x_4778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object* v_00_u03b1_4779_){
_start:
{
lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v_toApplicative_4782_; lean_object* v___x_4784_; uint8_t v_isShared_4785_; uint8_t v_isSharedCheck_4849_; 
v___x_4780_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0);
v___x_4781_ = l_StateRefT_x27_instMonad___redArg(v___x_4780_);
v_toApplicative_4782_ = lean_ctor_get(v___x_4781_, 0);
v_isSharedCheck_4849_ = !lean_is_exclusive(v___x_4781_);
if (v_isSharedCheck_4849_ == 0)
{
lean_object* v_unused_4850_; 
v_unused_4850_ = lean_ctor_get(v___x_4781_, 1);
lean_dec(v_unused_4850_);
v___x_4784_ = v___x_4781_;
v_isShared_4785_ = v_isSharedCheck_4849_;
goto v_resetjp_4783_;
}
else
{
lean_inc(v_toApplicative_4782_);
lean_dec(v___x_4781_);
v___x_4784_ = lean_box(0);
v_isShared_4785_ = v_isSharedCheck_4849_;
goto v_resetjp_4783_;
}
v_resetjp_4783_:
{
lean_object* v_toFunctor_4786_; lean_object* v_toSeq_4787_; lean_object* v_toSeqLeft_4788_; lean_object* v_toSeqRight_4789_; lean_object* v___x_4791_; uint8_t v_isShared_4792_; uint8_t v_isSharedCheck_4847_; 
v_toFunctor_4786_ = lean_ctor_get(v_toApplicative_4782_, 0);
v_toSeq_4787_ = lean_ctor_get(v_toApplicative_4782_, 2);
v_toSeqLeft_4788_ = lean_ctor_get(v_toApplicative_4782_, 3);
v_toSeqRight_4789_ = lean_ctor_get(v_toApplicative_4782_, 4);
v_isSharedCheck_4847_ = !lean_is_exclusive(v_toApplicative_4782_);
if (v_isSharedCheck_4847_ == 0)
{
lean_object* v_unused_4848_; 
v_unused_4848_ = lean_ctor_get(v_toApplicative_4782_, 1);
lean_dec(v_unused_4848_);
v___x_4791_ = v_toApplicative_4782_;
v_isShared_4792_ = v_isSharedCheck_4847_;
goto v_resetjp_4790_;
}
else
{
lean_inc(v_toSeqRight_4789_);
lean_inc(v_toSeqLeft_4788_);
lean_inc(v_toSeq_4787_);
lean_inc(v_toFunctor_4786_);
lean_dec(v_toApplicative_4782_);
v___x_4791_ = lean_box(0);
v_isShared_4792_ = v_isSharedCheck_4847_;
goto v_resetjp_4790_;
}
v_resetjp_4790_:
{
lean_object* v___f_4793_; lean_object* v___f_4794_; lean_object* v___f_4795_; lean_object* v___f_4796_; lean_object* v___x_4797_; lean_object* v___f_4798_; lean_object* v___f_4799_; lean_object* v___f_4800_; lean_object* v___x_4802_; 
v___f_4793_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1));
v___f_4794_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4786_);
v___f_4795_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4795_, 0, v_toFunctor_4786_);
v___f_4796_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4796_, 0, v_toFunctor_4786_);
v___x_4797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4797_, 0, v___f_4795_);
lean_ctor_set(v___x_4797_, 1, v___f_4796_);
v___f_4798_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4798_, 0, v_toSeqRight_4789_);
v___f_4799_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4799_, 0, v_toSeqLeft_4788_);
v___f_4800_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4800_, 0, v_toSeq_4787_);
if (v_isShared_4792_ == 0)
{
lean_ctor_set(v___x_4791_, 4, v___f_4798_);
lean_ctor_set(v___x_4791_, 3, v___f_4799_);
lean_ctor_set(v___x_4791_, 2, v___f_4800_);
lean_ctor_set(v___x_4791_, 1, v___f_4793_);
lean_ctor_set(v___x_4791_, 0, v___x_4797_);
v___x_4802_ = v___x_4791_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v___x_4797_);
lean_ctor_set(v_reuseFailAlloc_4846_, 1, v___f_4793_);
lean_ctor_set(v_reuseFailAlloc_4846_, 2, v___f_4800_);
lean_ctor_set(v_reuseFailAlloc_4846_, 3, v___f_4799_);
lean_ctor_set(v_reuseFailAlloc_4846_, 4, v___f_4798_);
v___x_4802_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
lean_object* v___x_4804_; 
if (v_isShared_4785_ == 0)
{
lean_ctor_set(v___x_4784_, 1, v___f_4794_);
lean_ctor_set(v___x_4784_, 0, v___x_4802_);
v___x_4804_ = v___x_4784_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v___x_4802_);
lean_ctor_set(v_reuseFailAlloc_4845_, 1, v___f_4794_);
v___x_4804_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
lean_object* v___x_4805_; lean_object* v_toApplicative_4806_; lean_object* v___x_4808_; uint8_t v_isShared_4809_; uint8_t v_isSharedCheck_4843_; 
v___x_4805_ = l_StateRefT_x27_instMonad___redArg(v___x_4804_);
v_toApplicative_4806_ = lean_ctor_get(v___x_4805_, 0);
v_isSharedCheck_4843_ = !lean_is_exclusive(v___x_4805_);
if (v_isSharedCheck_4843_ == 0)
{
lean_object* v_unused_4844_; 
v_unused_4844_ = lean_ctor_get(v___x_4805_, 1);
lean_dec(v_unused_4844_);
v___x_4808_ = v___x_4805_;
v_isShared_4809_ = v_isSharedCheck_4843_;
goto v_resetjp_4807_;
}
else
{
lean_inc(v_toApplicative_4806_);
lean_dec(v___x_4805_);
v___x_4808_ = lean_box(0);
v_isShared_4809_ = v_isSharedCheck_4843_;
goto v_resetjp_4807_;
}
v_resetjp_4807_:
{
lean_object* v_toFunctor_4810_; lean_object* v_toSeq_4811_; lean_object* v_toSeqLeft_4812_; lean_object* v_toSeqRight_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4841_; 
v_toFunctor_4810_ = lean_ctor_get(v_toApplicative_4806_, 0);
v_toSeq_4811_ = lean_ctor_get(v_toApplicative_4806_, 2);
v_toSeqLeft_4812_ = lean_ctor_get(v_toApplicative_4806_, 3);
v_toSeqRight_4813_ = lean_ctor_get(v_toApplicative_4806_, 4);
v_isSharedCheck_4841_ = !lean_is_exclusive(v_toApplicative_4806_);
if (v_isSharedCheck_4841_ == 0)
{
lean_object* v_unused_4842_; 
v_unused_4842_ = lean_ctor_get(v_toApplicative_4806_, 1);
lean_dec(v_unused_4842_);
v___x_4815_ = v_toApplicative_4806_;
v_isShared_4816_ = v_isSharedCheck_4841_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_toSeqRight_4813_);
lean_inc(v_toSeqLeft_4812_);
lean_inc(v_toSeq_4811_);
lean_inc(v_toFunctor_4810_);
lean_dec(v_toApplicative_4806_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4841_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v___f_4817_; lean_object* v___f_4818_; lean_object* v___f_4819_; lean_object* v___f_4820_; lean_object* v___x_4821_; lean_object* v___f_4822_; lean_object* v___f_4823_; lean_object* v___f_4824_; lean_object* v___x_4826_; 
v___f_4817_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3));
v___f_4818_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4810_);
v___f_4819_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4819_, 0, v_toFunctor_4810_);
v___f_4820_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4820_, 0, v_toFunctor_4810_);
v___x_4821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4821_, 0, v___f_4819_);
lean_ctor_set(v___x_4821_, 1, v___f_4820_);
v___f_4822_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4822_, 0, v_toSeqRight_4813_);
v___f_4823_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4823_, 0, v_toSeqLeft_4812_);
v___f_4824_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4824_, 0, v_toSeq_4811_);
if (v_isShared_4816_ == 0)
{
lean_ctor_set(v___x_4815_, 4, v___f_4822_);
lean_ctor_set(v___x_4815_, 3, v___f_4823_);
lean_ctor_set(v___x_4815_, 2, v___f_4824_);
lean_ctor_set(v___x_4815_, 1, v___f_4817_);
lean_ctor_set(v___x_4815_, 0, v___x_4821_);
v___x_4826_ = v___x_4815_;
goto v_reusejp_4825_;
}
else
{
lean_object* v_reuseFailAlloc_4840_; 
v_reuseFailAlloc_4840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4840_, 0, v___x_4821_);
lean_ctor_set(v_reuseFailAlloc_4840_, 1, v___f_4817_);
lean_ctor_set(v_reuseFailAlloc_4840_, 2, v___f_4824_);
lean_ctor_set(v_reuseFailAlloc_4840_, 3, v___f_4823_);
lean_ctor_set(v_reuseFailAlloc_4840_, 4, v___f_4822_);
v___x_4826_ = v_reuseFailAlloc_4840_;
goto v_reusejp_4825_;
}
v_reusejp_4825_:
{
lean_object* v___x_4828_; 
if (v_isShared_4809_ == 0)
{
lean_ctor_set(v___x_4808_, 1, v___f_4818_);
lean_ctor_set(v___x_4808_, 0, v___x_4826_);
v___x_4828_ = v___x_4808_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v___x_4826_);
lean_ctor_set(v_reuseFailAlloc_4839_, 1, v___f_4818_);
v___x_4828_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v_toMonadRef_4833_; lean_object* v___f_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; 
v___x_4829_ = l_StateRefT_x27_instMonad___redArg(v___x_4828_);
v___x_4830_ = l_ReaderT_instMonad___redArg(v___x_4829_);
v___x_4831_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__11, &l_Lean_Meta_Sym_instInhabitedSymM___closed__11_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__11);
v___x_4832_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__19, &l_Lean_Meta_Sym_instInhabitedSymM___closed__19_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__19);
v_toMonadRef_4833_ = lean_ctor_get(v___x_4832_, 0);
v___f_4834_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__21, &l_Lean_Meta_Sym_instInhabitedSymM___closed__21_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__21);
lean_inc_ref(v___x_4830_);
v___x_4835_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_4834_, v___x_4830_);
lean_inc_ref(v_toMonadRef_4833_);
v___x_4836_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4836_, 0, v___x_4831_);
lean_ctor_set(v___x_4836_, 1, v_toMonadRef_4833_);
lean_ctor_set(v___x_4836_, 2, v___x_4835_);
v___x_4837_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__23, &l_Lean_Meta_Sym_instInhabitedSymM___closed__23_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__23);
v___x_4838_ = l_Lean_throwError___redArg(v___x_4830_, v___x_4836_, v___x_4837_);
return v___x_4838_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(lean_object* v_ext_4851_, lean_object* v_extensions_4852_){
_start:
{
lean_object* v_id_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; 
v_id_4854_ = lean_ctor_get(v_ext_4851_, 0);
v___x_4855_ = l_Lean_Meta_Sym_instInhabitedSymExtensionState;
v___x_4856_ = lean_array_get_borrowed(v___x_4855_, v_extensions_4852_, v_id_4854_);
lean_inc(v___x_4856_);
v___x_4857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4857_, 0, v___x_4856_);
return v___x_4857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg___boxed(lean_object* v_ext_4858_, lean_object* v_extensions_4859_, lean_object* v_a_4860_){
_start:
{
lean_object* v_res_4861_; 
v_res_4861_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_4858_, v_extensions_4859_);
lean_dec_ref(v_extensions_4859_);
lean_dec_ref(v_ext_4858_);
return v_res_4861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(lean_object* v_00_u03c3_4862_, lean_object* v_ext_4863_, lean_object* v_extensions_4864_){
_start:
{
lean_object* v___x_4866_; 
v___x_4866_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_4863_, v_extensions_4864_);
return v___x_4866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___boxed(lean_object* v_00_u03c3_4867_, lean_object* v_ext_4868_, lean_object* v_extensions_4869_, lean_object* v_a_4870_){
_start:
{
lean_object* v_res_4871_; 
v_res_4871_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(v_00_u03c3_4867_, v_ext_4868_, v_extensions_4869_);
lean_dec_ref(v_extensions_4869_);
lean_dec_ref(v_ext_4868_);
return v_res_4871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg(lean_object* v_ext_4872_, lean_object* v_a_4873_, lean_object* v_a_4874_){
_start:
{
lean_object* v___x_4876_; lean_object* v_extensions_4877_; lean_object* v___x_4878_; 
v___x_4876_ = lean_st_ref_get(v_a_4873_);
v_extensions_4877_ = lean_ctor_get(v___x_4876_, 7);
lean_inc_ref(v_extensions_4877_);
lean_dec(v___x_4876_);
v___x_4878_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_4872_, v_extensions_4877_);
lean_dec_ref(v_extensions_4877_);
if (lean_obj_tag(v___x_4878_) == 0)
{
lean_object* v_a_4879_; lean_object* v___x_4881_; uint8_t v_isShared_4882_; uint8_t v_isSharedCheck_4886_; 
v_a_4879_ = lean_ctor_get(v___x_4878_, 0);
v_isSharedCheck_4886_ = !lean_is_exclusive(v___x_4878_);
if (v_isSharedCheck_4886_ == 0)
{
v___x_4881_ = v___x_4878_;
v_isShared_4882_ = v_isSharedCheck_4886_;
goto v_resetjp_4880_;
}
else
{
lean_inc(v_a_4879_);
lean_dec(v___x_4878_);
v___x_4881_ = lean_box(0);
v_isShared_4882_ = v_isSharedCheck_4886_;
goto v_resetjp_4880_;
}
v_resetjp_4880_:
{
lean_object* v___x_4884_; 
if (v_isShared_4882_ == 0)
{
v___x_4884_ = v___x_4881_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v_a_4879_);
v___x_4884_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
return v___x_4884_;
}
}
}
else
{
lean_object* v_a_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4899_; 
v_a_4887_ = lean_ctor_get(v___x_4878_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4878_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4889_ = v___x_4878_;
v_isShared_4890_ = v_isSharedCheck_4899_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_a_4887_);
lean_dec(v___x_4878_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4899_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
lean_object* v_ref_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4897_; 
v_ref_4891_ = lean_ctor_get(v_a_4874_, 5);
v___x_4892_ = lean_io_error_to_string(v_a_4887_);
v___x_4893_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4893_, 0, v___x_4892_);
v___x_4894_ = l_Lean_MessageData_ofFormat(v___x_4893_);
lean_inc(v_ref_4891_);
v___x_4895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4895_, 0, v_ref_4891_);
lean_ctor_set(v___x_4895_, 1, v___x_4894_);
if (v_isShared_4890_ == 0)
{
lean_ctor_set(v___x_4889_, 0, v___x_4895_);
v___x_4897_ = v___x_4889_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v___x_4895_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
return v___x_4897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg___boxed(lean_object* v_ext_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_){
_start:
{
lean_object* v_res_4904_; 
v_res_4904_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_4900_, v_a_4901_, v_a_4902_);
lean_dec_ref(v_a_4902_);
lean_dec(v_a_4901_);
lean_dec_ref(v_ext_4900_);
return v_res_4904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState(lean_object* v_00_u03c3_4905_, lean_object* v_ext_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_){
_start:
{
lean_object* v___x_4914_; 
v___x_4914_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_4906_, v_a_4908_, v_a_4911_);
return v___x_4914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___boxed(lean_object* v_00_u03c3_4915_, lean_object* v_ext_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_){
_start:
{
lean_object* v_res_4924_; 
v_res_4924_ = l_Lean_Meta_Sym_SymExtension_getState(v_00_u03c3_4915_, v_ext_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_);
lean_dec(v_a_4922_);
lean_dec_ref(v_a_4921_);
lean_dec(v_a_4920_);
lean_dec_ref(v_a_4919_);
lean_dec(v_a_4918_);
lean_dec_ref(v_a_4917_);
lean_dec_ref(v_ext_4916_);
return v_res_4924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(lean_object* v_ext_4925_, lean_object* v_f_4926_, lean_object* v_a_4927_){
_start:
{
lean_object* v___x_4929_; lean_object* v_share_4930_; lean_object* v_maxFVar_4931_; lean_object* v_proofInstInfo_4932_; lean_object* v_inferType_4933_; lean_object* v_getLevel_4934_; lean_object* v_congrInfo_4935_; lean_object* v_defEqI_4936_; lean_object* v_extensions_4937_; lean_object* v_issues_4938_; lean_object* v_canon_4939_; uint8_t v_debug_4940_; lean_object* v___x_4942_; uint8_t v_isShared_4943_; uint8_t v_isSharedCheck_4959_; 
v___x_4929_ = lean_st_ref_take(v_a_4927_);
v_share_4930_ = lean_ctor_get(v___x_4929_, 0);
v_maxFVar_4931_ = lean_ctor_get(v___x_4929_, 1);
v_proofInstInfo_4932_ = lean_ctor_get(v___x_4929_, 2);
v_inferType_4933_ = lean_ctor_get(v___x_4929_, 3);
v_getLevel_4934_ = lean_ctor_get(v___x_4929_, 4);
v_congrInfo_4935_ = lean_ctor_get(v___x_4929_, 5);
v_defEqI_4936_ = lean_ctor_get(v___x_4929_, 6);
v_extensions_4937_ = lean_ctor_get(v___x_4929_, 7);
v_issues_4938_ = lean_ctor_get(v___x_4929_, 8);
v_canon_4939_ = lean_ctor_get(v___x_4929_, 9);
v_debug_4940_ = lean_ctor_get_uint8(v___x_4929_, sizeof(void*)*10);
v_isSharedCheck_4959_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_4959_ == 0)
{
v___x_4942_ = v___x_4929_;
v_isShared_4943_ = v_isSharedCheck_4959_;
goto v_resetjp_4941_;
}
else
{
lean_inc(v_canon_4939_);
lean_inc(v_issues_4938_);
lean_inc(v_extensions_4937_);
lean_inc(v_defEqI_4936_);
lean_inc(v_congrInfo_4935_);
lean_inc(v_getLevel_4934_);
lean_inc(v_inferType_4933_);
lean_inc(v_proofInstInfo_4932_);
lean_inc(v_maxFVar_4931_);
lean_inc(v_share_4930_);
lean_dec(v___x_4929_);
v___x_4942_ = lean_box(0);
v_isShared_4943_ = v_isSharedCheck_4959_;
goto v_resetjp_4941_;
}
v_resetjp_4941_:
{
lean_object* v_id_4944_; lean_object* v___x_4945_; lean_object* v___y_4947_; lean_object* v___x_4953_; uint8_t v___x_4954_; 
v_id_4944_ = lean_ctor_get(v_ext_4925_, 0);
v___x_4945_ = lean_box(0);
v___x_4953_ = lean_array_get_size(v_extensions_4937_);
v___x_4954_ = lean_nat_dec_lt(v_id_4944_, v___x_4953_);
if (v___x_4954_ == 0)
{
lean_dec(v_f_4926_);
v___y_4947_ = v_extensions_4937_;
goto v___jp_4946_;
}
else
{
lean_object* v_v_4955_; lean_object* v_xs_x27_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; 
v_v_4955_ = lean_array_fget(v_extensions_4937_, v_id_4944_);
v_xs_x27_4956_ = lean_array_fset(v_extensions_4937_, v_id_4944_, v___x_4945_);
v___x_4957_ = lean_apply_1(v_f_4926_, v_v_4955_);
v___x_4958_ = lean_array_fset(v_xs_x27_4956_, v_id_4944_, v___x_4957_);
v___y_4947_ = v___x_4958_;
goto v___jp_4946_;
}
v___jp_4946_:
{
lean_object* v___x_4949_; 
if (v_isShared_4943_ == 0)
{
lean_ctor_set(v___x_4942_, 7, v___y_4947_);
v___x_4949_ = v___x_4942_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4952_; 
v_reuseFailAlloc_4952_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_4952_, 0, v_share_4930_);
lean_ctor_set(v_reuseFailAlloc_4952_, 1, v_maxFVar_4931_);
lean_ctor_set(v_reuseFailAlloc_4952_, 2, v_proofInstInfo_4932_);
lean_ctor_set(v_reuseFailAlloc_4952_, 3, v_inferType_4933_);
lean_ctor_set(v_reuseFailAlloc_4952_, 4, v_getLevel_4934_);
lean_ctor_set(v_reuseFailAlloc_4952_, 5, v_congrInfo_4935_);
lean_ctor_set(v_reuseFailAlloc_4952_, 6, v_defEqI_4936_);
lean_ctor_set(v_reuseFailAlloc_4952_, 7, v___y_4947_);
lean_ctor_set(v_reuseFailAlloc_4952_, 8, v_issues_4938_);
lean_ctor_set(v_reuseFailAlloc_4952_, 9, v_canon_4939_);
lean_ctor_set_uint8(v_reuseFailAlloc_4952_, sizeof(void*)*10, v_debug_4940_);
v___x_4949_ = v_reuseFailAlloc_4952_;
goto v_reusejp_4948_;
}
v_reusejp_4948_:
{
lean_object* v___x_4950_; lean_object* v___x_4951_; 
v___x_4950_ = lean_st_ref_set(v_a_4927_, v___x_4949_);
v___x_4951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4951_, 0, v___x_4945_);
return v___x_4951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg___boxed(lean_object* v_ext_4960_, lean_object* v_f_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_){
_start:
{
lean_object* v_res_4964_; 
v_res_4964_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_4960_, v_f_4961_, v_a_4962_);
lean_dec(v_a_4962_);
lean_dec_ref(v_ext_4960_);
return v_res_4964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(lean_object* v_00_u03c3_4965_, lean_object* v_ext_4966_, lean_object* v_f_4967_, lean_object* v_a_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_, lean_object* v_a_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_){
_start:
{
lean_object* v___x_4975_; 
v___x_4975_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_4966_, v_f_4967_, v_a_4969_);
return v___x_4975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___boxed(lean_object* v_00_u03c3_4976_, lean_object* v_ext_4977_, lean_object* v_f_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_){
_start:
{
lean_object* v_res_4986_; 
v_res_4986_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(v_00_u03c3_4976_, v_ext_4977_, v_f_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_);
lean_dec(v_a_4984_);
lean_dec_ref(v_a_4983_);
lean_dec(v_a_4982_);
lean_dec_ref(v_a_4981_);
lean_dec(v_a_4980_);
lean_dec_ref(v_a_4979_);
lean_dec_ref(v_ext_4977_);
return v_res_4986_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareCommon(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CongrTheorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_AlphaShareCommon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CongrTheorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Sym_sym_debug = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Sym_sym_debug);
lean_dec_ref(res);
res = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Sym_instInhabitedSymExtensionState = _init_l_Lean_Meta_Sym_instInhabitedSymExtensionState();
lean_mark_persistent(l_Lean_Meta_Sym_instInhabitedSymExtensionState);
res = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_SymM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_AlphaShareCommon(uint8_t builtin);
lean_object* initialize_Lean_Meta_CongrTheorems(uint8_t builtin);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_AlphaShareCommon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CongrTheorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_SymM(builtin);
}
#ifdef __cplusplus
}
#endif
