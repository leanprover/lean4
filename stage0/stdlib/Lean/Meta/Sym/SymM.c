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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_getStructureInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_mkProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Sym_isUnfoldReducibleCandidate(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_usize_mul(size_t, size_t);
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_initializing();
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_foldProjs___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___closed__2;
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "found `Expr.proj` with invalid field index `"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__1___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___closed__4;
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__1___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___closed__6;
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "found `Expr.proj` but `"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__1___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___closed__8;
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` is not marked as structure"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___closed__9 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__1___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___closed__10;
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
uint8_t v___x_178_; 
v___x_178_ = l_Lean_initializing();
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec_ref(v_mkInitial_176_);
v___x_179_ = lean_obj_once(&l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1, &l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1_once, _init_l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1);
v___x_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
return v___x_180_;
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_181_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef;
v___x_182_ = lean_st_ref_get(v___x_181_);
v___x_183_ = lean_st_ref_take(v___x_181_);
v___x_184_ = lean_array_get_size(v___x_182_);
lean_dec(v___x_182_);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v_mkInitial_176_);
lean_inc_ref(v___x_185_);
v___x_186_ = lean_array_push(v___x_183_, v___x_185_);
v___x_187_ = lean_st_ref_put(v___x_181_, v___x_186_);
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_185_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension___redArg___boxed(lean_object* v_mkInitial_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_Meta_Sym_registerSymExtension___redArg(v_mkInitial_189_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension(lean_object* v_00_u03c3_192_, lean_object* v_mkInitial_193_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_Meta_Sym_registerSymExtension___redArg(v_mkInitial_193_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension___boxed(lean_object* v_00_u03c3_196_, lean_object* v_mkInitial_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_Meta_Sym_registerSymExtension(v_00_u03c3_196_, v_mkInitial_197_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(size_t v_sz_200_, size_t v_i_201_, lean_object* v_bs_202_){
_start:
{
uint8_t v___x_204_; 
v___x_204_ = lean_usize_dec_lt(v_i_201_, v_sz_200_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; 
v___x_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_205_, 0, v_bs_202_);
return v___x_205_;
}
else
{
lean_object* v_v_206_; lean_object* v_mkInitial_207_; lean_object* v___x_208_; 
v_v_206_ = lean_array_uget_borrowed(v_bs_202_, v_i_201_);
v_mkInitial_207_ = lean_ctor_get(v_v_206_, 1);
lean_inc_ref(v_mkInitial_207_);
v___x_208_ = lean_apply_1(v_mkInitial_207_, lean_box(0));
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v___x_210_; lean_object* v_bs_x27_211_; size_t v___x_212_; size_t v___x_213_; lean_object* v___x_214_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_209_);
lean_dec_ref_known(v___x_208_, 1);
v___x_210_ = lean_unsigned_to_nat(0u);
v_bs_x27_211_ = lean_array_uset(v_bs_202_, v_i_201_, v___x_210_);
v___x_212_ = ((size_t)1ULL);
v___x_213_ = lean_usize_add(v_i_201_, v___x_212_);
v___x_214_ = lean_array_uset(v_bs_x27_211_, v_i_201_, v_a_209_);
v_i_201_ = v___x_213_;
v_bs_202_ = v___x_214_;
goto _start;
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
lean_dec_ref(v_bs_202_);
v_a_216_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_208_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_208_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_216_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0___boxed(lean_object* v_sz_224_, lean_object* v_i_225_, lean_object* v_bs_226_, lean_object* v___y_227_){
_start:
{
size_t v_sz_boxed_228_; size_t v_i_boxed_229_; lean_object* v_res_230_; 
v_sz_boxed_228_ = lean_unbox_usize(v_sz_224_);
lean_dec(v_sz_224_);
v_i_boxed_229_ = lean_unbox_usize(v_i_225_);
lean_dec(v_i_225_);
v_res_230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(v_sz_boxed_228_, v_i_boxed_229_, v_bs_226_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtensions_mkInitialStates(){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; size_t v_sz_234_; size_t v___x_235_; lean_object* v___x_236_; 
v___x_232_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef;
v___x_233_ = lean_st_ref_get(v___x_232_);
v_sz_234_ = lean_array_size(v___x_233_);
v___x_235_ = ((size_t)0ULL);
v___x_236_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(v_sz_234_, v___x_235_, v___x_233_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtensions_mkInitialStates___boxed(lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx(lean_object* v_x_247_){
_start:
{
switch(lean_obj_tag(v_x_247_))
{
case 0:
{
lean_object* v___x_248_; 
v___x_248_ = lean_unsigned_to_nat(0u);
return v___x_248_;
}
case 1:
{
lean_object* v___x_249_; 
v___x_249_ = lean_unsigned_to_nat(1u);
return v___x_249_;
}
case 2:
{
lean_object* v___x_250_; 
v___x_250_ = lean_unsigned_to_nat(2u);
return v___x_250_;
}
default: 
{
lean_object* v___x_251_; 
v___x_251_ = lean_unsigned_to_nat(3u);
return v___x_251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx___boxed(lean_object* v_x_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_Meta_Sym_CongrInfo_ctorIdx(v_x_252_);
lean_dec(v_x_252_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(lean_object* v_t_254_, lean_object* v_k_255_){
_start:
{
switch(lean_obj_tag(v_t_254_))
{
case 0:
{
return v_k_255_;
}
case 1:
{
lean_object* v_prefixSize_256_; lean_object* v_suffixSize_257_; lean_object* v___x_258_; 
v_prefixSize_256_ = lean_ctor_get(v_t_254_, 0);
lean_inc(v_prefixSize_256_);
v_suffixSize_257_ = lean_ctor_get(v_t_254_, 1);
lean_inc(v_suffixSize_257_);
lean_dec_ref_known(v_t_254_, 2);
v___x_258_ = lean_apply_2(v_k_255_, v_prefixSize_256_, v_suffixSize_257_);
return v___x_258_;
}
default: 
{
lean_object* v_rewritable_259_; lean_object* v___x_260_; 
v_rewritable_259_ = lean_ctor_get(v_t_254_, 0);
lean_inc_ref(v_rewritable_259_);
lean_dec(v_t_254_);
v___x_260_ = lean_apply_1(v_k_255_, v_rewritable_259_);
return v___x_260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim(lean_object* v_motive_261_, lean_object* v_ctorIdx_262_, lean_object* v_t_263_, lean_object* v_h_264_, lean_object* v_k_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_263_, v_k_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim___boxed(lean_object* v_motive_267_, lean_object* v_ctorIdx_268_, lean_object* v_t_269_, lean_object* v_h_270_, lean_object* v_k_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Meta_Sym_CongrInfo_ctorElim(v_motive_267_, v_ctorIdx_268_, v_t_269_, v_h_270_, v_k_271_);
lean_dec(v_ctorIdx_268_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_none_elim___redArg(lean_object* v_t_273_, lean_object* v_none_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_273_, v_none_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_none_elim(lean_object* v_motive_276_, lean_object* v_t_277_, lean_object* v_h_278_, lean_object* v_none_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_277_, v_none_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim___redArg(lean_object* v_t_281_, lean_object* v_fixedPrefix_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_281_, v_fixedPrefix_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim(lean_object* v_motive_284_, lean_object* v_t_285_, lean_object* v_h_286_, lean_object* v_fixedPrefix_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_285_, v_fixedPrefix_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_interlaced_elim___redArg(lean_object* v_t_289_, lean_object* v_interlaced_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_289_, v_interlaced_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_interlaced_elim(lean_object* v_motive_292_, lean_object* v_t_293_, lean_object* v_h_294_, lean_object* v_interlaced_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_293_, v_interlaced_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim___redArg(lean_object* v_t_297_, lean_object* v_congrTheorem_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_297_, v_congrTheorem_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim(lean_object* v_motive_300_, lean_object* v_t_301_, lean_object* v_h_302_, lean_object* v_congrTheorem_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_301_, v_congrTheorem_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducibleStep(lean_object* v_e_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_Expr_getAppFn(v_e_311_);
if (lean_obj_tag(v___x_317_) == 4)
{
lean_object* v_declName_318_; lean_object* v___x_319_; lean_object* v_env_320_; uint8_t v___x_321_; 
v_declName_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_declName_318_);
lean_dec_ref_known(v___x_317_, 2);
v___x_319_ = lean_st_ref_get(v_a_315_);
v_env_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc_ref(v_env_320_);
lean_dec(v___x_319_);
v___x_321_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_320_, v_declName_318_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; 
lean_dec_ref(v_e_311_);
v___x_322_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
else
{
uint8_t v___x_324_; lean_object* v___x_325_; 
v___x_324_ = 0;
v___x_325_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_311_, v___x_324_, v_a_312_, v_a_313_, v_a_314_, v_a_315_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_345_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_345_ == 0)
{
v___x_328_ = v___x_325_;
v_isShared_329_ = v_isSharedCheck_345_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_325_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_345_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
if (lean_obj_tag(v_a_326_) == 1)
{
lean_object* v_val_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_340_; 
v_val_330_ = lean_ctor_get(v_a_326_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v_a_326_);
if (v_isSharedCheck_340_ == 0)
{
v___x_332_ = v_a_326_;
v_isShared_333_ = v_isSharedCheck_340_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_val_330_);
lean_dec(v_a_326_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_340_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_val_330_);
v___x_335_ = v_reuseFailAlloc_339_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_337_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_335_);
v___x_337_ = v___x_328_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_335_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
else
{
lean_object* v___x_341_; lean_object* v___x_343_; 
lean_dec(v_a_326_);
v___x_341_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_341_);
v___x_343_ = v___x_328_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
v_a_346_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_325_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_325_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
else
{
lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec_ref(v___x_317_);
lean_dec_ref(v_e_311_);
v___x_354_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducibleStep___boxed(lean_object* v_e_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_Meta_Sym_unfoldReducibleStep(v_e_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
return v_res_362_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0(lean_object* v_env_363_, lean_object* v_e_364_){
_start:
{
if (lean_obj_tag(v_e_364_) == 4)
{
lean_object* v_declName_365_; uint8_t v___x_366_; 
v_declName_365_ = lean_ctor_get(v_e_364_, 0);
lean_inc(v_declName_365_);
lean_dec_ref_known(v_e_364_, 2);
v___x_366_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_363_, v_declName_365_);
return v___x_366_;
}
else
{
uint8_t v___x_367_; 
lean_dec_ref(v_e_364_);
lean_dec_ref(v_env_363_);
v___x_367_ = 0;
return v___x_367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0___boxed(lean_object* v_env_368_, lean_object* v_e_369_){
_start:
{
uint8_t v_res_370_; lean_object* v_r_371_; 
v_res_370_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0(v_env_368_, v_e_369_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(lean_object* v_e_372_, lean_object* v_a_373_){
_start:
{
lean_object* v___x_375_; lean_object* v_env_376_; lean_object* v___f_377_; lean_object* v___x_378_; 
v___x_375_ = lean_st_ref_get(v_a_373_);
v_env_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc_ref(v_env_376_);
lean_dec(v___x_375_);
v___f_377_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_377_, 0, v_env_376_);
v___x_378_ = lean_find_expr(v___f_377_, v_e_372_);
lean_dec_ref(v___f_377_);
if (lean_obj_tag(v___x_378_) == 0)
{
uint8_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = 0;
v___x_380_ = lean_box(v___x_379_);
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
return v___x_381_;
}
else
{
lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_390_; 
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_390_ == 0)
{
lean_object* v_unused_391_; 
v_unused_391_ = lean_ctor_get(v___x_378_, 0);
lean_dec(v_unused_391_);
v___x_383_ = v___x_378_;
v_isShared_384_ = v_isSharedCheck_390_;
goto v_resetjp_382_;
}
else
{
lean_dec(v___x_378_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_390_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
uint8_t v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_385_ = 1;
v___x_386_ = lean_box(v___x_385_);
if (v_isShared_384_ == 0)
{
lean_ctor_set_tag(v___x_383_, 0);
lean_ctor_set(v___x_383_, 0, v___x_386_);
v___x_388_ = v___x_383_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___boxed(lean_object* v_e_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_392_, v_a_393_);
lean_dec(v_a_393_);
lean_dec_ref(v_e_392_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget(lean_object* v_e_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_396_, v_a_398_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___boxed(lean_object* v_e_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget(v_e_401_, v_a_402_, v_a_403_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec_ref(v_e_401_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___lam__0(lean_object* v_e_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v_e_406_);
v___x_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___lam__0___boxed(lean_object* v_e_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_Meta_Sym_unfoldReducible___lam__0(v_e_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_object* v_00_u03b1_421_, lean_object* v_x_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_apply_1(v_x_422_, lean_box(0));
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0___boxed(lean_object* v_00_u03b1_430_, lean_object* v_x_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(v_00_u03b1_430_, v_x_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
return v_res_437_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(lean_object* v_a_438_, lean_object* v_x_439_){
_start:
{
if (lean_obj_tag(v_x_439_) == 0)
{
uint8_t v___x_440_; 
v___x_440_ = 0;
return v___x_440_;
}
else
{
lean_object* v_key_441_; lean_object* v_tail_442_; uint8_t v___x_443_; 
v_key_441_ = lean_ctor_get(v_x_439_, 0);
v_tail_442_ = lean_ctor_get(v_x_439_, 2);
v___x_443_ = l_Lean_ExprStructEq_beq(v_key_441_, v_a_438_);
if (v___x_443_ == 0)
{
v_x_439_ = v_tail_442_;
goto _start;
}
else
{
return v___x_443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object* v_a_445_, lean_object* v_x_446_){
_start:
{
uint8_t v_res_447_; lean_object* v_r_448_; 
v_res_447_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_445_, v_x_446_);
lean_dec(v_x_446_);
lean_dec_ref(v_a_445_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
if (lean_obj_tag(v_x_450_) == 0)
{
return v_x_449_;
}
else
{
lean_object* v_key_451_; lean_object* v_value_452_; lean_object* v_tail_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_476_; 
v_key_451_ = lean_ctor_get(v_x_450_, 0);
v_value_452_ = lean_ctor_get(v_x_450_, 1);
v_tail_453_ = lean_ctor_get(v_x_450_, 2);
v_isSharedCheck_476_ = !lean_is_exclusive(v_x_450_);
if (v_isSharedCheck_476_ == 0)
{
v___x_455_ = v_x_450_;
v_isShared_456_ = v_isSharedCheck_476_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_tail_453_);
lean_inc(v_value_452_);
lean_inc(v_key_451_);
lean_dec(v_x_450_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_476_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; uint64_t v___x_458_; uint64_t v___x_459_; uint64_t v___x_460_; uint64_t v_fold_461_; uint64_t v___x_462_; uint64_t v___x_463_; uint64_t v___x_464_; size_t v___x_465_; size_t v___x_466_; size_t v___x_467_; size_t v___x_468_; size_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_457_ = lean_array_get_size(v_x_449_);
v___x_458_ = l_Lean_ExprStructEq_hash(v_key_451_);
v___x_459_ = 32ULL;
v___x_460_ = lean_uint64_shift_right(v___x_458_, v___x_459_);
v_fold_461_ = lean_uint64_xor(v___x_458_, v___x_460_);
v___x_462_ = 16ULL;
v___x_463_ = lean_uint64_shift_right(v_fold_461_, v___x_462_);
v___x_464_ = lean_uint64_xor(v_fold_461_, v___x_463_);
v___x_465_ = lean_uint64_to_usize(v___x_464_);
v___x_466_ = lean_usize_of_nat(v___x_457_);
v___x_467_ = ((size_t)1ULL);
v___x_468_ = lean_usize_sub(v___x_466_, v___x_467_);
v___x_469_ = lean_usize_land(v___x_465_, v___x_468_);
v___x_470_ = lean_array_uget_borrowed(v_x_449_, v___x_469_);
lean_inc(v___x_470_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 2, v___x_470_);
v___x_472_ = v___x_455_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_key_451_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_value_452_);
lean_ctor_set(v_reuseFailAlloc_475_, 2, v___x_470_);
v___x_472_ = v_reuseFailAlloc_475_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
lean_object* v___x_473_; 
v___x_473_ = lean_array_uset(v_x_449_, v___x_469_, v___x_472_);
v_x_449_ = v___x_473_;
v_x_450_ = v_tail_453_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object* v_i_477_, lean_object* v_source_478_, lean_object* v_target_479_){
_start:
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = lean_array_get_size(v_source_478_);
v___x_481_ = lean_nat_dec_lt(v_i_477_, v___x_480_);
if (v___x_481_ == 0)
{
lean_dec_ref(v_source_478_);
lean_dec(v_i_477_);
return v_target_479_;
}
else
{
lean_object* v_es_482_; lean_object* v___x_483_; lean_object* v_source_484_; lean_object* v_target_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v_es_482_ = lean_array_fget(v_source_478_, v_i_477_);
v___x_483_ = lean_box(0);
v_source_484_ = lean_array_fset(v_source_478_, v_i_477_, v___x_483_);
v_target_485_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_479_, v_es_482_);
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = lean_nat_add(v_i_477_, v___x_486_);
lean_dec(v_i_477_);
v_i_477_ = v___x_487_;
v_source_478_ = v_source_484_;
v_target_479_ = v_target_485_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(lean_object* v_data_489_){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v_nbuckets_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_490_ = lean_array_get_size(v_data_489_);
v___x_491_ = lean_unsigned_to_nat(2u);
v_nbuckets_492_ = lean_nat_mul(v___x_490_, v___x_491_);
v___x_493_ = lean_unsigned_to_nat(0u);
v___x_494_ = lean_box(0);
v___x_495_ = lean_mk_array(v_nbuckets_492_, v___x_494_);
v___x_496_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_493_, v_data_489_, v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(lean_object* v_a_497_, lean_object* v_b_498_, lean_object* v_x_499_){
_start:
{
if (lean_obj_tag(v_x_499_) == 0)
{
lean_dec(v_b_498_);
lean_dec_ref(v_a_497_);
return v_x_499_;
}
else
{
lean_object* v_key_500_; lean_object* v_value_501_; lean_object* v_tail_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_514_; 
v_key_500_ = lean_ctor_get(v_x_499_, 0);
v_value_501_ = lean_ctor_get(v_x_499_, 1);
v_tail_502_ = lean_ctor_get(v_x_499_, 2);
v_isSharedCheck_514_ = !lean_is_exclusive(v_x_499_);
if (v_isSharedCheck_514_ == 0)
{
v___x_504_ = v_x_499_;
v_isShared_505_ = v_isSharedCheck_514_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_tail_502_);
lean_inc(v_value_501_);
lean_inc(v_key_500_);
lean_dec(v_x_499_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_514_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
uint8_t v___x_506_; 
v___x_506_ = l_Lean_ExprStructEq_beq(v_key_500_, v_a_497_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_509_; 
v___x_507_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_497_, v_b_498_, v_tail_502_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 2, v___x_507_);
v___x_509_ = v___x_504_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_key_500_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_value_501_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
else
{
lean_object* v___x_512_; 
lean_dec(v_value_501_);
lean_dec(v_key_500_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 1, v_b_498_);
lean_ctor_set(v___x_504_, 0, v_a_497_);
v___x_512_ = v___x_504_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_497_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_b_498_);
lean_ctor_set(v_reuseFailAlloc_513_, 2, v_tail_502_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(lean_object* v_m_515_, lean_object* v_a_516_, lean_object* v_b_517_){
_start:
{
lean_object* v_size_518_; lean_object* v_buckets_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_562_; 
v_size_518_ = lean_ctor_get(v_m_515_, 0);
v_buckets_519_ = lean_ctor_get(v_m_515_, 1);
v_isSharedCheck_562_ = !lean_is_exclusive(v_m_515_);
if (v_isSharedCheck_562_ == 0)
{
v___x_521_ = v_m_515_;
v_isShared_522_ = v_isSharedCheck_562_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_buckets_519_);
lean_inc(v_size_518_);
lean_dec(v_m_515_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_562_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; uint64_t v___x_524_; uint64_t v___x_525_; uint64_t v___x_526_; uint64_t v_fold_527_; uint64_t v___x_528_; uint64_t v___x_529_; uint64_t v___x_530_; size_t v___x_531_; size_t v___x_532_; size_t v___x_533_; size_t v___x_534_; size_t v___x_535_; lean_object* v_bkt_536_; uint8_t v___x_537_; 
v___x_523_ = lean_array_get_size(v_buckets_519_);
v___x_524_ = l_Lean_ExprStructEq_hash(v_a_516_);
v___x_525_ = 32ULL;
v___x_526_ = lean_uint64_shift_right(v___x_524_, v___x_525_);
v_fold_527_ = lean_uint64_xor(v___x_524_, v___x_526_);
v___x_528_ = 16ULL;
v___x_529_ = lean_uint64_shift_right(v_fold_527_, v___x_528_);
v___x_530_ = lean_uint64_xor(v_fold_527_, v___x_529_);
v___x_531_ = lean_uint64_to_usize(v___x_530_);
v___x_532_ = lean_usize_of_nat(v___x_523_);
v___x_533_ = ((size_t)1ULL);
v___x_534_ = lean_usize_sub(v___x_532_, v___x_533_);
v___x_535_ = lean_usize_land(v___x_531_, v___x_534_);
v_bkt_536_ = lean_array_uget_borrowed(v_buckets_519_, v___x_535_);
v___x_537_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_516_, v_bkt_536_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; lean_object* v_size_x27_539_; lean_object* v___x_540_; lean_object* v_buckets_x27_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_538_ = lean_unsigned_to_nat(1u);
v_size_x27_539_ = lean_nat_add(v_size_518_, v___x_538_);
lean_dec(v_size_518_);
lean_inc(v_bkt_536_);
v___x_540_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_540_, 0, v_a_516_);
lean_ctor_set(v___x_540_, 1, v_b_517_);
lean_ctor_set(v___x_540_, 2, v_bkt_536_);
v_buckets_x27_541_ = lean_array_uset(v_buckets_519_, v___x_535_, v___x_540_);
v___x_542_ = lean_unsigned_to_nat(4u);
v___x_543_ = lean_nat_mul(v_size_x27_539_, v___x_542_);
v___x_544_ = lean_unsigned_to_nat(3u);
v___x_545_ = lean_nat_div(v___x_543_, v___x_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_array_get_size(v_buckets_x27_541_);
v___x_547_ = lean_nat_dec_le(v___x_545_, v___x_546_);
lean_dec(v___x_545_);
if (v___x_547_ == 0)
{
lean_object* v_val_548_; lean_object* v___x_550_; 
v_val_548_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_541_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v_val_548_);
lean_ctor_set(v___x_521_, 0, v_size_x27_539_);
v___x_550_ = v___x_521_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_size_x27_539_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_val_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
else
{
lean_object* v___x_553_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v_buckets_x27_541_);
lean_ctor_set(v___x_521_, 0, v_size_x27_539_);
v___x_553_ = v___x_521_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_size_x27_539_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_buckets_x27_541_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
else
{
lean_object* v___x_555_; lean_object* v_buckets_x27_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_560_; 
lean_inc(v_bkt_536_);
v___x_555_ = lean_box(0);
v_buckets_x27_556_ = lean_array_uset(v_buckets_519_, v___x_535_, v___x_555_);
v___x_557_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_516_, v_b_517_, v_bkt_536_);
v___x_558_ = lean_array_uset(v_buckets_x27_556_, v___x_535_, v___x_557_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v___x_558_);
v___x_560_ = v___x_521_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_size_518_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(lean_object* v_a_563_, lean_object* v_e_564_, lean_object* v_a_565_){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_567_ = lean_st_ref_take(v_a_563_);
v___x_568_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v___x_567_, v_e_564_, v_a_565_);
v___x_569_ = lean_st_ref_put(v_a_563_, v___x_568_);
v___x_570_ = lean_box(0);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed(lean_object* v_a_571_, lean_object* v_e_572_, lean_object* v_a_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(v_a_571_, v_e_572_, v_a_573_);
lean_dec(v_a_571_);
return v_res_575_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = l_Lean_maxRecDepthErrorMessage;
v___x_582_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
return v___x_582_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
v___x_584_ = l_Lean_MessageData_ofFormat(v___x_583_);
return v___x_584_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
v___x_586_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2));
v___x_587_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v___x_585_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(lean_object* v_ref_588_){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_590_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v_ref_588_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object* v_ref_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_593_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(lean_object* v_x_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v___y_604_; lean_object* v_toCold_613_; lean_object* v_options_614_; lean_object* v_currRecDepth_615_; lean_object* v_maxRecDepth_616_; lean_object* v_ref_617_; lean_object* v_currNamespace_618_; lean_object* v_openDecls_619_; lean_object* v_initHeartbeats_620_; lean_object* v_maxHeartbeats_621_; lean_object* v_currMacroScope_622_; uint8_t v_diag_623_; uint8_t v_suppressElabErrors_624_; lean_object* v___x_630_; uint8_t v___x_631_; 
v_toCold_613_ = lean_ctor_get(v___y_600_, 0);
v_options_614_ = lean_ctor_get(v___y_600_, 1);
v_currRecDepth_615_ = lean_ctor_get(v___y_600_, 2);
v_maxRecDepth_616_ = lean_ctor_get(v___y_600_, 3);
v_ref_617_ = lean_ctor_get(v___y_600_, 4);
v_currNamespace_618_ = lean_ctor_get(v___y_600_, 5);
v_openDecls_619_ = lean_ctor_get(v___y_600_, 6);
v_initHeartbeats_620_ = lean_ctor_get(v___y_600_, 7);
v_maxHeartbeats_621_ = lean_ctor_get(v___y_600_, 8);
v_currMacroScope_622_ = lean_ctor_get(v___y_600_, 9);
v_diag_623_ = lean_ctor_get_uint8(v___y_600_, sizeof(void*)*10);
v_suppressElabErrors_624_ = lean_ctor_get_uint8(v___y_600_, sizeof(void*)*10 + 1);
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_nat_dec_eq(v_maxRecDepth_616_, v___x_630_);
if (v___x_631_ == 0)
{
uint8_t v___x_632_; 
v___x_632_ = lean_nat_dec_eq(v_currRecDepth_615_, v_maxRecDepth_616_);
if (v___x_632_ == 0)
{
goto v___jp_625_;
}
else
{
lean_object* v___x_633_; 
lean_dec_ref(v_x_596_);
lean_inc(v_ref_617_);
v___x_633_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_617_);
v___y_604_ = v___x_633_;
goto v___jp_603_;
}
}
else
{
goto v___jp_625_;
}
v___jp_603_:
{
if (lean_obj_tag(v___y_604_) == 0)
{
return v___y_604_;
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
v_a_605_ = lean_ctor_get(v___y_604_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___y_604_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___y_604_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___y_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
v___jp_625_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = lean_nat_add(v_currRecDepth_615_, v___x_626_);
lean_inc(v_currMacroScope_622_);
lean_inc(v_maxHeartbeats_621_);
lean_inc(v_initHeartbeats_620_);
lean_inc(v_openDecls_619_);
lean_inc(v_currNamespace_618_);
lean_inc(v_ref_617_);
lean_inc(v_maxRecDepth_616_);
lean_inc_ref(v_options_614_);
lean_inc_ref(v_toCold_613_);
v___x_628_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_628_, 0, v_toCold_613_);
lean_ctor_set(v___x_628_, 1, v_options_614_);
lean_ctor_set(v___x_628_, 2, v___x_627_);
lean_ctor_set(v___x_628_, 3, v_maxRecDepth_616_);
lean_ctor_set(v___x_628_, 4, v_ref_617_);
lean_ctor_set(v___x_628_, 5, v_currNamespace_618_);
lean_ctor_set(v___x_628_, 6, v_openDecls_619_);
lean_ctor_set(v___x_628_, 7, v_initHeartbeats_620_);
lean_ctor_set(v___x_628_, 8, v_maxHeartbeats_621_);
lean_ctor_set(v___x_628_, 9, v_currMacroScope_622_);
lean_ctor_set_uint8(v___x_628_, sizeof(void*)*10, v_diag_623_);
lean_ctor_set_uint8(v___x_628_, sizeof(void*)*10 + 1, v_suppressElabErrors_624_);
lean_inc(v___y_601_);
lean_inc(v___y_599_);
lean_inc_ref(v___y_598_);
lean_inc(v___y_597_);
v___x_629_ = lean_apply_6(v_x_596_, v___y_597_, v___y_598_, v___y_599_, v___x_628_, v___y_601_, lean_box(0));
v___y_604_ = v___x_629_;
goto v___jp_603_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg___boxed(lean_object* v_x_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_642_, lean_object* v_x_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_apply_1(v_x_643_, lean_box(0));
v___x_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_651_, lean_object* v_x_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(v_00_u03b1_651_, v_x_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_a_659_, lean_object* v_x_660_){
_start:
{
if (lean_obj_tag(v_x_660_) == 0)
{
lean_object* v___x_661_; 
v___x_661_ = lean_box(0);
return v___x_661_;
}
else
{
lean_object* v_key_662_; lean_object* v_value_663_; lean_object* v_tail_664_; uint8_t v___x_665_; 
v_key_662_ = lean_ctor_get(v_x_660_, 0);
v_value_663_ = lean_ctor_get(v_x_660_, 1);
v_tail_664_ = lean_ctor_get(v_x_660_, 2);
v___x_665_ = l_Lean_ExprStructEq_beq(v_key_662_, v_a_659_);
if (v___x_665_ == 0)
{
v_x_660_ = v_tail_664_;
goto _start;
}
else
{
lean_object* v___x_667_; 
lean_inc(v_value_663_);
v___x_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_667_, 0, v_value_663_);
return v___x_667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_a_668_, lean_object* v_x_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_668_, v_x_669_);
lean_dec(v_x_669_);
lean_dec_ref(v_a_668_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(lean_object* v_m_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_buckets_673_; lean_object* v___x_674_; uint64_t v___x_675_; uint64_t v___x_676_; uint64_t v___x_677_; uint64_t v_fold_678_; uint64_t v___x_679_; uint64_t v___x_680_; uint64_t v___x_681_; size_t v___x_682_; size_t v___x_683_; size_t v___x_684_; size_t v___x_685_; size_t v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v_buckets_673_ = lean_ctor_get(v_m_671_, 1);
v___x_674_ = lean_array_get_size(v_buckets_673_);
v___x_675_ = l_Lean_ExprStructEq_hash(v_a_672_);
v___x_676_ = 32ULL;
v___x_677_ = lean_uint64_shift_right(v___x_675_, v___x_676_);
v_fold_678_ = lean_uint64_xor(v___x_675_, v___x_677_);
v___x_679_ = 16ULL;
v___x_680_ = lean_uint64_shift_right(v_fold_678_, v___x_679_);
v___x_681_ = lean_uint64_xor(v_fold_678_, v___x_680_);
v___x_682_ = lean_uint64_to_usize(v___x_681_);
v___x_683_ = lean_usize_of_nat(v___x_674_);
v___x_684_ = ((size_t)1ULL);
v___x_685_ = lean_usize_sub(v___x_683_, v___x_684_);
v___x_686_ = lean_usize_land(v___x_682_, v___x_685_);
v___x_687_ = lean_array_uget_borrowed(v_buckets_673_, v___x_686_);
v___x_688_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_672_, v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_m_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_m_689_, v_a_690_);
lean_dec_ref(v_a_690_);
lean_dec_ref(v_m_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(lean_object* v___x_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_692_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object* v___x_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(v___x_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object* v_k_706_, lean_object* v___y_707_, lean_object* v_b_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v___x_714_; 
lean_inc(v___y_712_);
lean_inc_ref(v___y_711_);
lean_inc(v___y_710_);
lean_inc_ref(v___y_709_);
lean_inc(v___y_707_);
v___x_714_ = lean_apply_7(v_k_706_, v_b_708_, v___y_707_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, lean_box(0));
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_715_, lean_object* v___y_716_, lean_object* v_b_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_715_, v___y_716_, v_b_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_716_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_name_724_, uint8_t v_bi_725_, lean_object* v_type_726_, lean_object* v_k_727_, uint8_t v_kind_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___f_735_; lean_object* v___x_736_; 
lean_inc(v___y_729_);
v___f_735_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_735_, 0, v_k_727_);
lean_closure_set(v___f_735_, 1, v___y_729_);
v___x_736_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_724_, v_bi_725_, v_type_726_, v___f_735_, v_kind_728_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
if (lean_obj_tag(v___x_736_) == 0)
{
return v___x_736_;
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_name_745_, lean_object* v_bi_746_, lean_object* v_type_747_, lean_object* v_k_748_, lean_object* v_kind_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
uint8_t v_bi_boxed_756_; uint8_t v_kind_boxed_757_; lean_object* v_res_758_; 
v_bi_boxed_756_ = lean_unbox(v_bi_746_);
v_kind_boxed_757_ = lean_unbox(v_kind_749_);
v_res_758_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_745_, v_bi_boxed_756_, v_type_747_, v_k_748_, v_kind_boxed_757_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(lean_object* v_name_759_, lean_object* v_type_760_, lean_object* v_val_761_, lean_object* v_k_762_, uint8_t v_nondep_763_, uint8_t v_kind_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v___f_771_; lean_object* v___x_772_; 
lean_inc(v___y_765_);
v___f_771_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_771_, 0, v_k_762_);
lean_closure_set(v___f_771_, 1, v___y_765_);
v___x_772_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_759_, v_type_760_, v_val_761_, v___f_771_, v_nondep_763_, v_kind_764_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
if (lean_obj_tag(v___x_772_) == 0)
{
return v___x_772_;
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_772_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_772_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object* v_name_781_, lean_object* v_type_782_, lean_object* v_val_783_, lean_object* v_k_784_, lean_object* v_nondep_785_, lean_object* v_kind_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
uint8_t v_nondep_boxed_793_; uint8_t v_kind_boxed_794_; lean_object* v_res_795_; 
v_nondep_boxed_793_ = lean_unbox(v_nondep_785_);
v_kind_boxed_794_ = lean_unbox(v_kind_786_);
v_res_795_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_781_, v_type_782_, v_val_783_, v_k_784_, v_nondep_boxed_793_, v_kind_boxed_794_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(lean_object* v_fvars_799_, lean_object* v_pre_800_, lean_object* v_post_801_, uint8_t v_usedLetOnly_802_, uint8_t v_skipConstInApp_803_, uint8_t v_skipInstances_804_, lean_object* v_body_805_, lean_object* v_x_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_array_push(v_fvars_799_, v_x_806_);
v___x_814_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_800_, v_post_801_, v_usedLetOnly_802_, v_skipConstInApp_803_, v_skipInstances_804_, v___x_813_, v_body_805_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed(lean_object* v_fvars_815_, lean_object* v_pre_816_, lean_object* v_post_817_, lean_object* v_usedLetOnly_818_, lean_object* v_skipConstInApp_819_, lean_object* v_skipInstances_820_, lean_object* v_body_821_, lean_object* v_x_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
uint8_t v_usedLetOnly_boxed_829_; uint8_t v_skipConstInApp_boxed_830_; uint8_t v_skipInstances_boxed_831_; lean_object* v_res_832_; 
v_usedLetOnly_boxed_829_ = lean_unbox(v_usedLetOnly_818_);
v_skipConstInApp_boxed_830_ = lean_unbox(v_skipConstInApp_819_);
v_skipInstances_boxed_831_ = lean_unbox(v_skipInstances_820_);
v_res_832_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(v_fvars_815_, v_pre_816_, v_post_817_, v_usedLetOnly_boxed_829_, v_skipConstInApp_boxed_830_, v_skipInstances_boxed_831_, v_body_821_, v_x_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(lean_object* v_pre_833_, lean_object* v_post_834_, uint8_t v_usedLetOnly_835_, uint8_t v_skipConstInApp_836_, uint8_t v_skipInstances_837_, lean_object* v_e_838_, lean_object* v_a_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v___x_845_; 
lean_inc_ref(v_post_834_);
lean_inc(v___y_843_);
lean_inc_ref(v___y_842_);
lean_inc(v___y_841_);
lean_inc_ref(v___y_840_);
lean_inc_ref(v_e_838_);
v___x_845_ = lean_apply_6(v_post_834_, v_e_838_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, lean_box(0));
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_864_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_864_ == 0)
{
v___x_848_ = v___x_845_;
v_isShared_849_ = v_isSharedCheck_864_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_845_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_864_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
switch(lean_obj_tag(v_a_846_))
{
case 0:
{
lean_object* v_e_850_; lean_object* v___x_852_; 
lean_dec_ref(v_e_838_);
lean_dec_ref(v_post_834_);
lean_dec_ref(v_pre_833_);
v_e_850_ = lean_ctor_get(v_a_846_, 0);
lean_inc_ref(v_e_850_);
lean_dec_ref_known(v_a_846_, 1);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v_e_850_);
v___x_852_ = v___x_848_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_e_850_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
case 1:
{
lean_object* v_e_854_; lean_object* v___x_855_; 
lean_del_object(v___x_848_);
lean_dec_ref(v_e_838_);
v_e_854_ = lean_ctor_get(v_a_846_, 0);
lean_inc_ref(v_e_854_);
lean_dec_ref_known(v_a_846_, 1);
v___x_855_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_833_, v_post_834_, v_usedLetOnly_835_, v_skipConstInApp_836_, v_skipInstances_837_, v_e_854_, v_a_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
return v___x_855_;
}
default: 
{
lean_object* v_e_x3f_856_; 
lean_dec_ref(v_post_834_);
lean_dec_ref(v_pre_833_);
v_e_x3f_856_ = lean_ctor_get(v_a_846_, 0);
lean_inc(v_e_x3f_856_);
lean_dec_ref_known(v_a_846_, 1);
if (lean_obj_tag(v_e_x3f_856_) == 0)
{
lean_object* v___x_858_; 
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v_e_838_);
v___x_858_ = v___x_848_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_e_838_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
else
{
lean_object* v_val_860_; lean_object* v___x_862_; 
lean_dec_ref(v_e_838_);
v_val_860_ = lean_ctor_get(v_e_x3f_856_, 0);
lean_inc(v_val_860_);
lean_dec_ref_known(v_e_x3f_856_, 1);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v_val_860_);
v___x_862_ = v___x_848_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_val_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec_ref(v_e_838_);
lean_dec_ref(v_post_834_);
lean_dec_ref(v_pre_833_);
v_a_865_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_845_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_845_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(lean_object* v_pre_873_, lean_object* v_post_874_, uint8_t v_usedLetOnly_875_, uint8_t v_skipConstInApp_876_, uint8_t v_skipInstances_877_, lean_object* v_fvars_878_, lean_object* v_e_879_, lean_object* v_a_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
if (lean_obj_tag(v_e_879_) == 6)
{
lean_object* v_binderName_886_; lean_object* v_binderType_887_; lean_object* v_body_888_; uint8_t v_binderInfo_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v_binderName_886_ = lean_ctor_get(v_e_879_, 0);
lean_inc(v_binderName_886_);
v_binderType_887_ = lean_ctor_get(v_e_879_, 1);
lean_inc_ref(v_binderType_887_);
v_body_888_ = lean_ctor_get(v_e_879_, 2);
lean_inc_ref(v_body_888_);
v_binderInfo_889_ = lean_ctor_get_uint8(v_e_879_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_879_, 3);
v___x_890_ = lean_expr_instantiate_rev(v_binderType_887_, v_fvars_878_);
lean_dec_ref(v_binderType_887_);
lean_inc_ref(v_post_874_);
lean_inc_ref(v_pre_873_);
v___x_891_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_873_, v_post_874_, v_usedLetOnly_875_, v_skipConstInApp_876_, v_skipInstances_877_, v___x_890_, v_a_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___f_896_; uint8_t v___x_897_; lean_object* v___x_898_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_a_892_);
lean_dec_ref_known(v___x_891_, 1);
v___x_893_ = lean_box(v_usedLetOnly_875_);
v___x_894_ = lean_box(v_skipConstInApp_876_);
v___x_895_ = lean_box(v_skipInstances_877_);
v___f_896_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_896_, 0, v_fvars_878_);
lean_closure_set(v___f_896_, 1, v_pre_873_);
lean_closure_set(v___f_896_, 2, v_post_874_);
lean_closure_set(v___f_896_, 3, v___x_893_);
lean_closure_set(v___f_896_, 4, v___x_894_);
lean_closure_set(v___f_896_, 5, v___x_895_);
lean_closure_set(v___f_896_, 6, v_body_888_);
v___x_897_ = 0;
v___x_898_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_886_, v_binderInfo_889_, v_a_892_, v___f_896_, v___x_897_, v_a_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
return v___x_898_;
}
else
{
lean_dec_ref(v_body_888_);
lean_dec(v_binderName_886_);
lean_dec_ref(v_fvars_878_);
lean_dec_ref(v_post_874_);
lean_dec_ref(v_pre_873_);
return v___x_891_;
}
}
else
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = lean_expr_instantiate_rev(v_e_879_, v_fvars_878_);
lean_dec_ref(v_e_879_);
lean_inc_ref(v_post_874_);
lean_inc_ref(v_pre_873_);
v___x_900_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_873_, v_post_874_, v_usedLetOnly_875_, v_skipConstInApp_876_, v_skipInstances_877_, v___x_899_, v_a_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; uint8_t v___x_902_; uint8_t v___x_903_; uint8_t v___x_904_; lean_object* v___x_905_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_901_);
lean_dec_ref_known(v___x_900_, 1);
v___x_902_ = 0;
v___x_903_ = 1;
v___x_904_ = 1;
v___x_905_ = l_Lean_Meta_mkLambdaFVars(v_fvars_878_, v_a_901_, v___x_902_, v_usedLetOnly_875_, v___x_902_, v___x_903_, v___x_904_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
lean_dec_ref(v_fvars_878_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_907_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_a_906_);
lean_dec_ref_known(v___x_905_, 1);
v___x_907_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_873_, v_post_874_, v_usedLetOnly_875_, v_skipConstInApp_876_, v_skipInstances_877_, v_a_906_, v_a_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
return v___x_907_;
}
else
{
lean_dec_ref(v_post_874_);
lean_dec_ref(v_pre_873_);
return v___x_905_;
}
}
else
{
lean_dec_ref(v_fvars_878_);
lean_dec_ref(v_post_874_);
lean_dec_ref(v_pre_873_);
return v___x_900_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(lean_object* v_fvars_908_, lean_object* v_pre_909_, lean_object* v_post_910_, uint8_t v_usedLetOnly_911_, uint8_t v_skipConstInApp_912_, uint8_t v_skipInstances_913_, lean_object* v_body_914_, lean_object* v_x_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_array_push(v_fvars_908_, v_x_915_);
v___x_923_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_909_, v_post_910_, v_usedLetOnly_911_, v_skipConstInApp_912_, v_skipInstances_913_, v___x_922_, v_body_914_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed(lean_object* v_fvars_924_, lean_object* v_pre_925_, lean_object* v_post_926_, lean_object* v_usedLetOnly_927_, lean_object* v_skipConstInApp_928_, lean_object* v_skipInstances_929_, lean_object* v_body_930_, lean_object* v_x_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
uint8_t v_usedLetOnly_boxed_938_; uint8_t v_skipConstInApp_boxed_939_; uint8_t v_skipInstances_boxed_940_; lean_object* v_res_941_; 
v_usedLetOnly_boxed_938_ = lean_unbox(v_usedLetOnly_927_);
v_skipConstInApp_boxed_939_ = lean_unbox(v_skipConstInApp_928_);
v_skipInstances_boxed_940_ = lean_unbox(v_skipInstances_929_);
v_res_941_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(v_fvars_924_, v_pre_925_, v_post_926_, v_usedLetOnly_boxed_938_, v_skipConstInApp_boxed_939_, v_skipInstances_boxed_940_, v_body_930_, v_x_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(lean_object* v_pre_942_, lean_object* v_post_943_, uint8_t v_usedLetOnly_944_, uint8_t v_skipConstInApp_945_, uint8_t v_skipInstances_946_, lean_object* v_fvars_947_, lean_object* v_e_948_, lean_object* v_a_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
if (lean_obj_tag(v_e_948_) == 8)
{
lean_object* v_declName_955_; lean_object* v_type_956_; lean_object* v_value_957_; lean_object* v_body_958_; uint8_t v_nondep_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v_declName_955_ = lean_ctor_get(v_e_948_, 0);
lean_inc(v_declName_955_);
v_type_956_ = lean_ctor_get(v_e_948_, 1);
lean_inc_ref(v_type_956_);
v_value_957_ = lean_ctor_get(v_e_948_, 2);
lean_inc_ref(v_value_957_);
v_body_958_ = lean_ctor_get(v_e_948_, 3);
lean_inc_ref(v_body_958_);
v_nondep_959_ = lean_ctor_get_uint8(v_e_948_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_948_, 4);
v___x_960_ = lean_expr_instantiate_rev(v_type_956_, v_fvars_947_);
lean_dec_ref(v_type_956_);
lean_inc_ref(v_post_943_);
lean_inc_ref(v_pre_942_);
v___x_961_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_942_, v_post_943_, v_usedLetOnly_944_, v_skipConstInApp_945_, v_skipInstances_946_, v___x_960_, v_a_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref_known(v___x_961_, 1);
v___x_963_ = lean_expr_instantiate_rev(v_value_957_, v_fvars_947_);
lean_dec_ref(v_value_957_);
lean_inc_ref(v_post_943_);
lean_inc_ref(v_pre_942_);
v___x_964_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_942_, v_post_943_, v_usedLetOnly_944_, v_skipConstInApp_945_, v_skipInstances_946_, v___x_963_, v_a_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___f_969_; uint8_t v___x_970_; lean_object* v___x_971_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref_known(v___x_964_, 1);
v___x_966_ = lean_box(v_usedLetOnly_944_);
v___x_967_ = lean_box(v_skipConstInApp_945_);
v___x_968_ = lean_box(v_skipInstances_946_);
v___f_969_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_969_, 0, v_fvars_947_);
lean_closure_set(v___f_969_, 1, v_pre_942_);
lean_closure_set(v___f_969_, 2, v_post_943_);
lean_closure_set(v___f_969_, 3, v___x_966_);
lean_closure_set(v___f_969_, 4, v___x_967_);
lean_closure_set(v___f_969_, 5, v___x_968_);
lean_closure_set(v___f_969_, 6, v_body_958_);
v___x_970_ = 0;
v___x_971_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_955_, v_a_962_, v_a_965_, v___f_969_, v_nondep_959_, v___x_970_, v_a_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
return v___x_971_;
}
else
{
lean_dec(v_a_962_);
lean_dec_ref(v_body_958_);
lean_dec(v_declName_955_);
lean_dec_ref(v_fvars_947_);
lean_dec_ref(v_post_943_);
lean_dec_ref(v_pre_942_);
return v___x_964_;
}
}
else
{
lean_dec_ref(v_body_958_);
lean_dec_ref(v_value_957_);
lean_dec(v_declName_955_);
lean_dec_ref(v_fvars_947_);
lean_dec_ref(v_post_943_);
lean_dec_ref(v_pre_942_);
return v___x_961_;
}
}
else
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = lean_expr_instantiate_rev(v_e_948_, v_fvars_947_);
lean_dec_ref(v_e_948_);
lean_inc_ref(v_post_943_);
lean_inc_ref(v_pre_942_);
v___x_973_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_942_, v_post_943_, v_usedLetOnly_944_, v_skipConstInApp_945_, v_skipInstances_946_, v___x_972_, v_a_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; uint8_t v___x_975_; uint8_t v___x_976_; lean_object* v___x_977_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref_known(v___x_973_, 1);
v___x_975_ = 0;
v___x_976_ = 1;
v___x_977_ = l_Lean_Meta_mkLetFVars(v_fvars_947_, v_a_974_, v_usedLetOnly_944_, v___x_975_, v___x_976_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
lean_dec_ref(v_fvars_947_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_979_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref_known(v___x_977_, 1);
v___x_979_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_942_, v_post_943_, v_usedLetOnly_944_, v_skipConstInApp_945_, v_skipInstances_946_, v_a_978_, v_a_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
return v___x_979_;
}
else
{
lean_dec_ref(v_post_943_);
lean_dec_ref(v_pre_942_);
return v___x_977_;
}
}
else
{
lean_dec_ref(v_fvars_947_);
lean_dec_ref(v_post_943_);
lean_dec_ref(v_pre_942_);
return v___x_973_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1(void){
_start:
{
lean_object* v___x_980_; lean_object* v_dummy_981_; 
v___x_980_ = lean_box(0);
v_dummy_981_ = l_Lean_Expr_sort___override(v___x_980_);
return v_dummy_981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(lean_object* v_pre_982_, lean_object* v_post_983_, uint8_t v_usedLetOnly_984_, uint8_t v_skipConstInApp_985_, uint8_t v_skipInstances_986_, size_t v_sz_987_, size_t v_i_988_, lean_object* v_bs_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
uint8_t v___x_996_; 
v___x_996_ = lean_usize_dec_lt(v_i_988_, v_sz_987_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; 
lean_dec_ref(v_post_983_);
lean_dec_ref(v_pre_982_);
v___x_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_997_, 0, v_bs_989_);
return v___x_997_;
}
else
{
lean_object* v_v_998_; lean_object* v___x_999_; 
v_v_998_ = lean_array_uget_borrowed(v_bs_989_, v_i_988_);
lean_inc(v_v_998_);
lean_inc_ref(v_post_983_);
lean_inc_ref(v_pre_982_);
v___x_999_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_982_, v_post_983_, v_usedLetOnly_984_, v_skipConstInApp_985_, v_skipInstances_986_, v_v_998_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; lean_object* v_bs_x27_1002_; size_t v___x_1003_; size_t v___x_1004_; lean_object* v___x_1005_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_999_, 1);
v___x_1001_ = lean_unsigned_to_nat(0u);
v_bs_x27_1002_ = lean_array_uset(v_bs_989_, v_i_988_, v___x_1001_);
v___x_1003_ = ((size_t)1ULL);
v___x_1004_ = lean_usize_add(v_i_988_, v___x_1003_);
v___x_1005_ = lean_array_uset(v_bs_x27_1002_, v_i_988_, v_a_1000_);
v_i_988_ = v___x_1004_;
v_bs_989_ = v___x_1005_;
goto _start;
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec_ref(v_bs_989_);
lean_dec_ref(v_post_983_);
lean_dec_ref(v_pre_982_);
v_a_1007_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_999_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_999_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_pre_1015_, lean_object* v_post_1016_, uint8_t v_usedLetOnly_1017_, uint8_t v_skipConstInApp_1018_, uint8_t v_skipInstances_1019_, lean_object* v___x_1020_, lean_object* v___y_1021_, lean_object* v_b_1022_, lean_object* v_a_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1015_, v_post_1016_, v_usedLetOnly_1017_, v_skipConstInApp_1018_, v_skipInstances_1019_, v___x_1020_, v___y_1021_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1039_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1032_ = v___x_1029_;
v_isShared_1033_ = v_isSharedCheck_1039_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1029_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1039_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1034_ = lean_array_fset(v_b_1022_, v_a_1023_, v_a_1030_);
v___x_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v___x_1035_);
v___x_1037_ = v___x_1032_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_dec_ref(v_b_1022_);
v_a_1040_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_1029_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1029_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_pre_1048_, lean_object* v_post_1049_, lean_object* v_usedLetOnly_1050_, lean_object* v_skipConstInApp_1051_, lean_object* v_skipInstances_1052_, lean_object* v___x_1053_, lean_object* v___y_1054_, lean_object* v_b_1055_, lean_object* v_a_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
uint8_t v_usedLetOnly_boxed_1062_; uint8_t v_skipConstInApp_boxed_1063_; uint8_t v_skipInstances_boxed_1064_; lean_object* v_res_1065_; 
v_usedLetOnly_boxed_1062_ = lean_unbox(v_usedLetOnly_1050_);
v_skipConstInApp_boxed_1063_ = lean_unbox(v_skipConstInApp_1051_);
v_skipInstances_boxed_1064_ = lean_unbox(v_skipInstances_1052_);
v_res_1065_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_1048_, v_post_1049_, v_usedLetOnly_boxed_1062_, v_skipConstInApp_boxed_1063_, v_skipInstances_boxed_1064_, v___x_1053_, v___y_1054_, v_b_1055_, v_a_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v_a_1056_);
lean_dec(v___y_1054_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(lean_object* v_upperBound_1066_, lean_object* v___x_1067_, lean_object* v_pre_1068_, lean_object* v_post_1069_, uint8_t v_usedLetOnly_1070_, uint8_t v_skipConstInApp_1071_, uint8_t v_skipInstances_1072_, lean_object* v_a_1073_, lean_object* v_b_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v___y_1082_; uint8_t v___x_1105_; 
v___x_1105_ = lean_nat_dec_lt(v_a_1073_, v_upperBound_1066_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; 
lean_dec(v_a_1073_);
lean_dec_ref(v_post_1069_);
lean_dec_ref(v_pre_1068_);
v___x_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1106_, 0, v_b_1074_);
return v___x_1106_;
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1107_ = lean_array_fget_borrowed(v_b_1074_, v_a_1073_);
v___x_1108_ = lean_array_get_size(v___x_1067_);
v___x_1109_ = lean_nat_dec_lt(v_a_1073_, v___x_1108_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___f_1113_; 
lean_inc(v___x_1107_);
v___x_1110_ = lean_box(v_usedLetOnly_1070_);
v___x_1111_ = lean_box(v_skipConstInApp_1071_);
v___x_1112_ = lean_box(v_skipInstances_1072_);
lean_inc(v_a_1073_);
lean_inc(v___y_1075_);
lean_inc_ref(v_post_1069_);
lean_inc_ref(v_pre_1068_);
v___f_1113_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1113_, 0, v_pre_1068_);
lean_closure_set(v___f_1113_, 1, v_post_1069_);
lean_closure_set(v___f_1113_, 2, v___x_1110_);
lean_closure_set(v___f_1113_, 3, v___x_1111_);
lean_closure_set(v___f_1113_, 4, v___x_1112_);
lean_closure_set(v___f_1113_, 5, v___x_1107_);
lean_closure_set(v___f_1113_, 6, v___y_1075_);
lean_closure_set(v___f_1113_, 7, v_b_1074_);
lean_closure_set(v___f_1113_, 8, v_a_1073_);
v___y_1082_ = v___f_1113_;
goto v___jp_1081_;
}
else
{
lean_object* v___x_1114_; uint8_t v_isInstance_1115_; 
v___x_1114_ = lean_array_fget_borrowed(v___x_1067_, v_a_1073_);
v_isInstance_1115_ = lean_ctor_get_uint8(v___x_1114_, sizeof(void*)*1 + 4);
if (v_isInstance_1115_ == 0)
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___f_1119_; 
lean_inc(v___x_1107_);
v___x_1116_ = lean_box(v_usedLetOnly_1070_);
v___x_1117_ = lean_box(v_skipConstInApp_1071_);
v___x_1118_ = lean_box(v_skipInstances_1072_);
lean_inc(v_a_1073_);
lean_inc(v___y_1075_);
lean_inc_ref(v_post_1069_);
lean_inc_ref(v_pre_1068_);
v___f_1119_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1119_, 0, v_pre_1068_);
lean_closure_set(v___f_1119_, 1, v_post_1069_);
lean_closure_set(v___f_1119_, 2, v___x_1116_);
lean_closure_set(v___f_1119_, 3, v___x_1117_);
lean_closure_set(v___f_1119_, 4, v___x_1118_);
lean_closure_set(v___f_1119_, 5, v___x_1107_);
lean_closure_set(v___f_1119_, 6, v___y_1075_);
lean_closure_set(v___f_1119_, 7, v_b_1074_);
lean_closure_set(v___f_1119_, 8, v_a_1073_);
v___y_1082_ = v___f_1119_;
goto v___jp_1081_;
}
else
{
lean_object* v___x_1120_; lean_object* v___f_1121_; 
v___x_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1120_, 0, v_b_1074_);
v___f_1121_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1121_, 0, v___x_1120_);
v___y_1082_ = v___f_1121_;
goto v___jp_1081_;
}
}
}
v___jp_1081_:
{
lean_object* v___x_1083_; 
lean_inc(v___y_1079_);
lean_inc_ref(v___y_1078_);
lean_inc(v___y_1077_);
lean_inc_ref(v___y_1076_);
v___x_1083_ = lean_apply_5(v___y_1082_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, lean_box(0));
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1096_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1086_ = v___x_1083_;
v_isShared_1087_ = v_isSharedCheck_1096_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1083_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1096_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
if (lean_obj_tag(v_a_1084_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1090_; 
lean_dec(v_a_1073_);
lean_dec_ref(v_post_1069_);
lean_dec_ref(v_pre_1068_);
v_a_1088_ = lean_ctor_get(v_a_1084_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v_a_1084_, 1);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v_a_1088_);
v___x_1090_ = v___x_1086_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_del_object(v___x_1086_);
v_a_1092_ = lean_ctor_get(v_a_1084_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v_a_1084_, 1);
v___x_1093_ = lean_unsigned_to_nat(1u);
v___x_1094_ = lean_nat_add(v_a_1073_, v___x_1093_);
lean_dec(v_a_1073_);
v_a_1073_ = v___x_1094_;
v_b_1074_ = v_a_1092_;
goto _start;
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec(v_a_1073_);
lean_dec_ref(v_post_1069_);
lean_dec_ref(v_pre_1068_);
v_a_1097_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1083_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1083_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(uint8_t v_skipInstances_1122_, lean_object* v_pre_1123_, lean_object* v_post_1124_, uint8_t v_usedLetOnly_1125_, uint8_t v_skipConstInApp_1126_, lean_object* v_x_1127_, lean_object* v_x_1128_, lean_object* v_x_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_f_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; 
if (lean_obj_tag(v_x_1127_) == 5)
{
lean_object* v_fn_1185_; lean_object* v_arg_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v_fn_1185_ = lean_ctor_get(v_x_1127_, 0);
lean_inc_ref(v_fn_1185_);
v_arg_1186_ = lean_ctor_get(v_x_1127_, 1);
lean_inc_ref(v_arg_1186_);
lean_dec_ref_known(v_x_1127_, 2);
v___x_1187_ = lean_array_set(v_x_1128_, v_x_1129_, v_arg_1186_);
v___x_1188_ = lean_unsigned_to_nat(1u);
v___x_1189_ = lean_nat_sub(v_x_1129_, v___x_1188_);
lean_dec(v_x_1129_);
v_x_1127_ = v_fn_1185_;
v_x_1128_ = v___x_1187_;
v_x_1129_ = v___x_1189_;
goto _start;
}
else
{
lean_dec(v_x_1129_);
if (v_skipConstInApp_1126_ == 0)
{
goto v___jp_1182_;
}
else
{
uint8_t v___x_1191_; 
v___x_1191_ = l_Lean_Expr_isConst(v_x_1127_);
if (v___x_1191_ == 0)
{
goto v___jp_1182_;
}
else
{
v_f_1137_ = v_x_1127_;
v___y_1138_ = v___y_1130_;
v___y_1139_ = v___y_1131_;
v___y_1140_ = v___y_1132_;
v___y_1141_ = v___y_1133_;
v___y_1142_ = v___y_1134_;
goto v___jp_1136_;
}
}
}
v___jp_1136_:
{
if (v_skipInstances_1122_ == 0)
{
size_t v_sz_1143_; size_t v___x_1144_; lean_object* v___x_1145_; 
v_sz_1143_ = lean_array_size(v_x_1128_);
v___x_1144_ = ((size_t)0ULL);
lean_inc_ref(v_post_1124_);
lean_inc_ref(v_pre_1123_);
v___x_1145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_pre_1123_, v_post_1124_, v_usedLetOnly_1125_, v_skipConstInApp_1126_, v_skipInstances_1122_, v_sz_1143_, v___x_1144_, v_x_1128_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1145_, 1);
v___x_1147_ = l_Lean_mkAppN(v_f_1137_, v_a_1146_);
lean_dec(v_a_1146_);
v___x_1148_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1123_, v_post_1124_, v_usedLetOnly_1125_, v_skipConstInApp_1126_, v_skipInstances_1122_, v___x_1147_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
return v___x_1148_;
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_dec_ref(v_f_1137_);
lean_dec_ref(v_post_1124_);
lean_dec_ref(v_pre_1123_);
v_a_1149_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1145_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1145_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = lean_array_get_size(v_x_1128_);
lean_inc_ref(v_f_1137_);
v___x_1158_ = l_Lean_Meta_getFunInfoNArgs(v_f_1137_, v___x_1157_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v_paramInfo_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1158_, 1);
v_paramInfo_1160_ = lean_ctor_get(v_a_1159_, 0);
lean_inc_ref(v_paramInfo_1160_);
lean_dec(v_a_1159_);
v___x_1161_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1124_);
lean_inc_ref(v_pre_1123_);
v___x_1162_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v___x_1157_, v_paramInfo_1160_, v_pre_1123_, v_post_1124_, v_usedLetOnly_1125_, v_skipConstInApp_1126_, v_skipInstances_1122_, v___x_1161_, v_x_1128_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
lean_dec_ref(v_paramInfo_1160_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v___x_1164_ = l_Lean_mkAppN(v_f_1137_, v_a_1163_);
lean_dec(v_a_1163_);
v___x_1165_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1123_, v_post_1124_, v_usedLetOnly_1125_, v_skipConstInApp_1126_, v_skipInstances_1122_, v___x_1164_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
return v___x_1165_;
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
lean_dec_ref(v_f_1137_);
lean_dec_ref(v_post_1124_);
lean_dec_ref(v_pre_1123_);
v_a_1166_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1162_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1162_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
else
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
lean_dec_ref(v_f_1137_);
lean_dec_ref(v_x_1128_);
lean_dec_ref(v_post_1124_);
lean_dec_ref(v_pre_1123_);
v_a_1174_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1158_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1158_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
}
v___jp_1182_:
{
lean_object* v___x_1183_; 
lean_inc_ref(v_post_1124_);
lean_inc_ref(v_pre_1123_);
v___x_1183_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1123_, v_post_1124_, v_usedLetOnly_1125_, v_skipConstInApp_1126_, v_skipInstances_1122_, v_x_1127_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1183_, 1);
v_f_1137_ = v_a_1184_;
v___y_1138_ = v___y_1130_;
v___y_1139_ = v___y_1131_;
v___y_1140_ = v___y_1132_;
v___y_1141_ = v___y_1133_;
v___y_1142_ = v___y_1134_;
goto v___jp_1136_;
}
else
{
lean_dec_ref(v_x_1128_);
lean_dec_ref(v_post_1124_);
lean_dec_ref(v_pre_1123_);
return v___x_1183_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(lean_object* v___x_1192_, lean_object* v_pre_1193_, lean_object* v_e_1194_, lean_object* v_post_1195_, uint8_t v_usedLetOnly_1196_, uint8_t v_skipConstInApp_1197_, uint8_t v_skipInstances_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lean_Core_checkSystem(v___x_1192_, v___y_1202_, v___y_1203_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v___x_1206_; 
lean_dec_ref_known(v___x_1205_, 1);
lean_inc_ref(v_pre_1193_);
lean_inc(v___y_1203_);
lean_inc_ref(v___y_1202_);
lean_inc(v___y_1201_);
lean_inc_ref(v___y_1200_);
lean_inc_ref(v_e_1194_);
v___x_1206_ = lean_apply_6(v_pre_1193_, v_e_1194_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, lean_box(0));
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1255_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1209_ = v___x_1206_;
v_isShared_1210_ = v_isSharedCheck_1255_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1206_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1255_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___y_1212_; 
switch(lean_obj_tag(v_a_1207_))
{
case 0:
{
lean_object* v_e_1247_; lean_object* v___x_1249_; 
lean_dec_ref(v_post_1195_);
lean_dec_ref(v_e_1194_);
lean_dec_ref(v_pre_1193_);
v_e_1247_ = lean_ctor_get(v_a_1207_, 0);
lean_inc_ref(v_e_1247_);
lean_dec_ref_known(v_a_1207_, 1);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 0, v_e_1247_);
v___x_1249_ = v___x_1209_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_e_1247_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
case 1:
{
lean_object* v_e_1251_; lean_object* v___x_1252_; 
lean_del_object(v___x_1209_);
lean_dec_ref(v_e_1194_);
v_e_1251_ = lean_ctor_get(v_a_1207_, 0);
lean_inc_ref(v_e_1251_);
lean_dec_ref_known(v_a_1207_, 1);
v___x_1252_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1193_, v_post_1195_, v_usedLetOnly_1196_, v_skipConstInApp_1197_, v_skipInstances_1198_, v_e_1251_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
return v___x_1252_;
}
default: 
{
lean_object* v_e_x3f_1253_; 
lean_del_object(v___x_1209_);
v_e_x3f_1253_ = lean_ctor_get(v_a_1207_, 0);
lean_inc(v_e_x3f_1253_);
lean_dec_ref_known(v_a_1207_, 1);
if (lean_obj_tag(v_e_x3f_1253_) == 0)
{
v___y_1212_ = v_e_1194_;
goto v___jp_1211_;
}
else
{
lean_object* v_val_1254_; 
lean_dec_ref(v_e_1194_);
v_val_1254_ = lean_ctor_get(v_e_x3f_1253_, 0);
lean_inc(v_val_1254_);
lean_dec_ref_known(v_e_x3f_1253_, 1);
v___y_1212_ = v_val_1254_;
goto v___jp_1211_;
}
}
}
v___jp_1211_:
{
switch(lean_obj_tag(v___y_1212_))
{
case 7:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1214_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1193_, v_post_1195_, v_usedLetOnly_1196_, v_skipConstInApp_1197_, v_skipInstances_1198_, v___x_1213_, v___y_1212_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
return v___x_1214_;
}
case 6:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1216_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_1193_, v_post_1195_, v_usedLetOnly_1196_, v_skipConstInApp_1197_, v_skipInstances_1198_, v___x_1215_, v___y_1212_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
return v___x_1216_;
}
case 8:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1218_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_1193_, v_post_1195_, v_usedLetOnly_1196_, v_skipConstInApp_1197_, v_skipInstances_1198_, v___x_1217_, v___y_1212_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
return v___x_1218_;
}
case 5:
{
lean_object* v_dummy_1219_; lean_object* v_nargs_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v_dummy_1219_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1);
v_nargs_1220_ = l_Lean_Expr_getAppNumArgs(v___y_1212_);
lean_inc(v_nargs_1220_);
v___x_1221_ = lean_mk_array(v_nargs_1220_, v_dummy_1219_);
v___x_1222_ = lean_unsigned_to_nat(1u);
v___x_1223_ = lean_nat_sub(v_nargs_1220_, v___x_1222_);
lean_dec(v_nargs_1220_);
v___x_1224_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_1198_, v_pre_1193_, v_post_1195_, v_usedLetOnly_1196_, v_skipConstInApp_1197_, v___y_1212_, v___x_1221_, v___x_1223_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
return v___x_1224_;
}
case 10:
{
lean_object* v_data_1225_; lean_object* v_expr_1226_; lean_object* v___x_1227_; 
v_data_1225_ = lean_ctor_get(v___y_1212_, 0);
v_expr_1226_ = lean_ctor_get(v___y_1212_, 1);
lean_inc_ref(v_expr_1226_);
lean_inc_ref(v_post_1195_);
lean_inc_ref(v_pre_1193_);
v___x_1227_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1193_, v_post_1195_, v_usedLetOnly_1196_, v_skipConstInApp_1197_, v_skipInstances_1198_, v_expr_1226_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; size_t v___x_1229_; size_t v___x_1230_; uint8_t v___x_1231_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1228_);
lean_dec_ref_known(v___x_1227_, 1);
v___x_1229_ = lean_ptr_addr(v_expr_1226_);
v___x_1230_ = lean_ptr_addr(v_a_1228_);
v___x_1231_ = lean_usize_dec_eq(v___x_1229_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
lean_inc(v_data_1225_);
lean_dec_ref_known(v___y_1212_, 2);
v___x_1232_ = l_Lean_Expr_mdata___override(v_data_1225_, v_a_1228_);
v___x_1233_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1193_, v_post_1195_, v_usedLetOnly_1196_, v_skipConstInApp_1197_, v_skipInstances_1198_, v___x_1232_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
return v___x_1233_;
}
else
{
lean_object* v___x_1234_; 
lean_dec(v_a_1228_);
v___x_1234_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1193_, v_post_1195_, v_usedLetOnly_1196_, v_skipConstInApp_1197_, v_skipInstances_1198_, v___y_1212_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
return v___x_1234_;
}
}
else
{
lean_dec_ref_known(v___y_1212_, 2);
lean_dec_ref(v_post_1195_);
lean_dec_ref(v_pre_1193_);
return v___x_1227_;
}
}
case 11:
{
lean_object* v_typeName_1235_; lean_object* v_idx_1236_; lean_object* v_struct_1237_; lean_object* v___x_1238_; 
v_typeName_1235_ = lean_ctor_get(v___y_1212_, 0);
v_idx_1236_ = lean_ctor_get(v___y_1212_, 1);
v_struct_1237_ = lean_ctor_get(v___y_1212_, 2);
lean_inc_ref(v_struct_1237_);
lean_inc_ref(v_post_1195_);
lean_inc_ref(v_pre_1193_);
v___x_1238_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1193_, v_post_1195_, v_usedLetOnly_1196_, v_skipConstInApp_1197_, v_skipInstances_1198_, v_struct_1237_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; size_t v___x_1240_; size_t v___x_1241_; uint8_t v___x_1242_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref_known(v___x_1238_, 1);
v___x_1240_ = lean_ptr_addr(v_struct_1237_);
v___x_1241_ = lean_ptr_addr(v_a_1239_);
v___x_1242_ = lean_usize_dec_eq(v___x_1240_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_inc(v_idx_1236_);
lean_inc(v_typeName_1235_);
lean_dec_ref_known(v___y_1212_, 3);
v___x_1243_ = l_Lean_Expr_proj___override(v_typeName_1235_, v_idx_1236_, v_a_1239_);
v___x_1244_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1193_, v_post_1195_, v_usedLetOnly_1196_, v_skipConstInApp_1197_, v_skipInstances_1198_, v___x_1243_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
return v___x_1244_;
}
else
{
lean_object* v___x_1245_; 
lean_dec(v_a_1239_);
v___x_1245_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1193_, v_post_1195_, v_usedLetOnly_1196_, v_skipConstInApp_1197_, v_skipInstances_1198_, v___y_1212_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
return v___x_1245_;
}
}
else
{
lean_dec_ref_known(v___y_1212_, 3);
lean_dec_ref(v_post_1195_);
lean_dec_ref(v_pre_1193_);
return v___x_1238_;
}
}
default: 
{
lean_object* v___x_1246_; 
v___x_1246_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1193_, v_post_1195_, v_usedLetOnly_1196_, v_skipConstInApp_1197_, v_skipInstances_1198_, v___y_1212_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
return v___x_1246_;
}
}
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec_ref(v_post_1195_);
lean_dec_ref(v_e_1194_);
lean_dec_ref(v_pre_1193_);
v_a_1256_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1206_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1206_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec_ref(v_post_1195_);
lean_dec_ref(v_e_1194_);
lean_dec_ref(v_pre_1193_);
v_a_1264_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1205_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1205_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1272_, lean_object* v_pre_1273_, lean_object* v_e_1274_, lean_object* v_post_1275_, lean_object* v_usedLetOnly_1276_, lean_object* v_skipConstInApp_1277_, lean_object* v_skipInstances_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
uint8_t v_usedLetOnly_boxed_1285_; uint8_t v_skipConstInApp_boxed_1286_; uint8_t v_skipInstances_boxed_1287_; lean_object* v_res_1288_; 
v_usedLetOnly_boxed_1285_ = lean_unbox(v_usedLetOnly_1276_);
v_skipConstInApp_boxed_1286_ = lean_unbox(v_skipConstInApp_1277_);
v_skipInstances_boxed_1287_ = lean_unbox(v_skipInstances_1278_);
v_res_1288_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(v___x_1272_, v_pre_1273_, v_e_1274_, v_post_1275_, v_usedLetOnly_boxed_1285_, v_skipConstInApp_boxed_1286_, v_skipInstances_boxed_1287_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(lean_object* v_pre_1289_, lean_object* v_post_1290_, uint8_t v_usedLetOnly_1291_, uint8_t v_skipConstInApp_1292_, uint8_t v_skipInstances_1293_, lean_object* v_e_1294_, lean_object* v_a_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
lean_inc(v_a_1295_);
v___x_1301_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1301_, 0, lean_box(0));
lean_closure_set(v___x_1301_, 1, lean_box(0));
lean_closure_set(v___x_1301_, 2, v_a_1295_);
v___x_1302_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v___x_1301_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1337_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1305_ = v___x_1302_;
v_isShared_1306_ = v_isSharedCheck_1337_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1302_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1337_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_a_1303_, v_e_1294_);
lean_dec(v_a_1303_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___f_1312_; lean_object* v___x_1313_; 
lean_del_object(v___x_1305_);
v___x_1308_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0));
v___x_1309_ = lean_box(v_usedLetOnly_1291_);
v___x_1310_ = lean_box(v_skipConstInApp_1292_);
v___x_1311_ = lean_box(v_skipInstances_1293_);
lean_inc_ref(v_e_1294_);
v___f_1312_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed), 13, 7);
lean_closure_set(v___f_1312_, 0, v___x_1308_);
lean_closure_set(v___f_1312_, 1, v_pre_1289_);
lean_closure_set(v___f_1312_, 2, v_e_1294_);
lean_closure_set(v___f_1312_, 3, v_post_1290_);
lean_closure_set(v___f_1312_, 4, v___x_1309_);
lean_closure_set(v___f_1312_, 5, v___x_1310_);
lean_closure_set(v___f_1312_, 6, v___x_1311_);
v___x_1313_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v___f_1312_, v_a_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v___f_1315_; lean_object* v___x_1316_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc_n(v_a_1314_, 2);
lean_dec_ref_known(v___x_1313_, 1);
lean_inc(v_a_1295_);
v___f_1315_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1315_, 0, v_a_1295_);
lean_closure_set(v___f_1315_, 1, v_e_1294_);
lean_closure_set(v___f_1315_, 2, v_a_1314_);
v___x_1316_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v___f_1315_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1323_ == 0)
{
lean_object* v_unused_1324_; 
v_unused_1324_ = lean_ctor_get(v___x_1316_, 0);
lean_dec(v_unused_1324_);
v___x_1318_ = v___x_1316_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_dec(v___x_1316_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v_a_1314_);
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1314_);
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
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec(v_a_1314_);
v_a_1325_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1316_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1316_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
else
{
lean_dec_ref(v_e_1294_);
return v___x_1313_;
}
}
else
{
lean_object* v_val_1333_; lean_object* v___x_1335_; 
lean_dec_ref(v_e_1294_);
lean_dec_ref(v_post_1290_);
lean_dec_ref(v_pre_1289_);
v_val_1333_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_val_1333_);
lean_dec_ref_known(v___x_1307_, 1);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 0, v_val_1333_);
v___x_1335_ = v___x_1305_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_val_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
lean_dec_ref(v_e_1294_);
lean_dec_ref(v_post_1290_);
lean_dec_ref(v_pre_1289_);
v_a_1338_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1302_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1302_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed(lean_object* v_fvars_1346_, lean_object* v_pre_1347_, lean_object* v_post_1348_, lean_object* v_usedLetOnly_1349_, lean_object* v_skipConstInApp_1350_, lean_object* v_skipInstances_1351_, lean_object* v_body_1352_, lean_object* v_x_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
uint8_t v_usedLetOnly_boxed_1360_; uint8_t v_skipConstInApp_boxed_1361_; uint8_t v_skipInstances_boxed_1362_; lean_object* v_res_1363_; 
v_usedLetOnly_boxed_1360_ = lean_unbox(v_usedLetOnly_1349_);
v_skipConstInApp_boxed_1361_ = lean_unbox(v_skipConstInApp_1350_);
v_skipInstances_boxed_1362_ = lean_unbox(v_skipInstances_1351_);
v_res_1363_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(v_fvars_1346_, v_pre_1347_, v_post_1348_, v_usedLetOnly_boxed_1360_, v_skipConstInApp_boxed_1361_, v_skipInstances_boxed_1362_, v_body_1352_, v_x_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(lean_object* v_pre_1364_, lean_object* v_post_1365_, uint8_t v_usedLetOnly_1366_, uint8_t v_skipConstInApp_1367_, uint8_t v_skipInstances_1368_, lean_object* v_fvars_1369_, lean_object* v_e_1370_, lean_object* v_a_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
if (lean_obj_tag(v_e_1370_) == 7)
{
lean_object* v_binderName_1377_; lean_object* v_binderType_1378_; lean_object* v_body_1379_; uint8_t v_binderInfo_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v_binderName_1377_ = lean_ctor_get(v_e_1370_, 0);
lean_inc(v_binderName_1377_);
v_binderType_1378_ = lean_ctor_get(v_e_1370_, 1);
lean_inc_ref(v_binderType_1378_);
v_body_1379_ = lean_ctor_get(v_e_1370_, 2);
lean_inc_ref(v_body_1379_);
v_binderInfo_1380_ = lean_ctor_get_uint8(v_e_1370_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1370_, 3);
v___x_1381_ = lean_expr_instantiate_rev(v_binderType_1378_, v_fvars_1369_);
lean_dec_ref(v_binderType_1378_);
lean_inc_ref(v_post_1365_);
lean_inc_ref(v_pre_1364_);
v___x_1382_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1364_, v_post_1365_, v_usedLetOnly_1366_, v_skipConstInApp_1367_, v_skipInstances_1368_, v___x_1381_, v_a_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___f_1387_; uint8_t v___x_1388_; lean_object* v___x_1389_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1383_);
lean_dec_ref_known(v___x_1382_, 1);
v___x_1384_ = lean_box(v_usedLetOnly_1366_);
v___x_1385_ = lean_box(v_skipConstInApp_1367_);
v___x_1386_ = lean_box(v_skipInstances_1368_);
v___f_1387_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1387_, 0, v_fvars_1369_);
lean_closure_set(v___f_1387_, 1, v_pre_1364_);
lean_closure_set(v___f_1387_, 2, v_post_1365_);
lean_closure_set(v___f_1387_, 3, v___x_1384_);
lean_closure_set(v___f_1387_, 4, v___x_1385_);
lean_closure_set(v___f_1387_, 5, v___x_1386_);
lean_closure_set(v___f_1387_, 6, v_body_1379_);
v___x_1388_ = 0;
v___x_1389_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_1377_, v_binderInfo_1380_, v_a_1383_, v___f_1387_, v___x_1388_, v_a_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
return v___x_1389_;
}
else
{
lean_dec_ref(v_body_1379_);
lean_dec(v_binderName_1377_);
lean_dec_ref(v_fvars_1369_);
lean_dec_ref(v_post_1365_);
lean_dec_ref(v_pre_1364_);
return v___x_1382_;
}
}
else
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = lean_expr_instantiate_rev(v_e_1370_, v_fvars_1369_);
lean_dec_ref(v_e_1370_);
lean_inc_ref(v_post_1365_);
lean_inc_ref(v_pre_1364_);
v___x_1391_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1364_, v_post_1365_, v_usedLetOnly_1366_, v_skipConstInApp_1367_, v_skipInstances_1368_, v___x_1390_, v_a_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; uint8_t v___x_1393_; uint8_t v___x_1394_; uint8_t v___x_1395_; lean_object* v___x_1396_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
v___x_1393_ = 0;
v___x_1394_ = 1;
v___x_1395_ = 1;
v___x_1396_ = l_Lean_Meta_mkForallFVars(v_fvars_1369_, v_a_1392_, v___x_1393_, v_usedLetOnly_1366_, v___x_1394_, v___x_1395_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
lean_dec_ref(v_fvars_1369_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v___x_1398_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1397_);
lean_dec_ref_known(v___x_1396_, 1);
v___x_1398_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1364_, v_post_1365_, v_usedLetOnly_1366_, v_skipConstInApp_1367_, v_skipInstances_1368_, v_a_1397_, v_a_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
return v___x_1398_;
}
else
{
lean_dec_ref(v_post_1365_);
lean_dec_ref(v_pre_1364_);
return v___x_1396_;
}
}
else
{
lean_dec_ref(v_fvars_1369_);
lean_dec_ref(v_post_1365_);
lean_dec_ref(v_pre_1364_);
return v___x_1391_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(lean_object* v_fvars_1399_, lean_object* v_pre_1400_, lean_object* v_post_1401_, uint8_t v_usedLetOnly_1402_, uint8_t v_skipConstInApp_1403_, uint8_t v_skipInstances_1404_, lean_object* v_body_1405_, lean_object* v_x_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = lean_array_push(v_fvars_1399_, v_x_1406_);
v___x_1414_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1400_, v_post_1401_, v_usedLetOnly_1402_, v_skipConstInApp_1403_, v_skipInstances_1404_, v___x_1413_, v_body_1405_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1415_, lean_object* v_post_1416_, lean_object* v_usedLetOnly_1417_, lean_object* v_skipConstInApp_1418_, lean_object* v_skipInstances_1419_, lean_object* v_e_1420_, lean_object* v_a_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
uint8_t v_usedLetOnly_boxed_1427_; uint8_t v_skipConstInApp_boxed_1428_; uint8_t v_skipInstances_boxed_1429_; lean_object* v_res_1430_; 
v_usedLetOnly_boxed_1427_ = lean_unbox(v_usedLetOnly_1417_);
v_skipConstInApp_boxed_1428_ = lean_unbox(v_skipConstInApp_1418_);
v_skipInstances_boxed_1429_ = lean_unbox(v_skipInstances_1419_);
v_res_1430_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1415_, v_post_1416_, v_usedLetOnly_boxed_1427_, v_skipConstInApp_boxed_1428_, v_skipInstances_boxed_1429_, v_e_1420_, v_a_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v_a_1421_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1431_, lean_object* v_post_1432_, lean_object* v_usedLetOnly_1433_, lean_object* v_skipConstInApp_1434_, lean_object* v_skipInstances_1435_, lean_object* v_sz_1436_, lean_object* v_i_1437_, lean_object* v_bs_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
uint8_t v_usedLetOnly_boxed_1445_; uint8_t v_skipConstInApp_boxed_1446_; uint8_t v_skipInstances_boxed_1447_; size_t v_sz_boxed_1448_; size_t v_i_boxed_1449_; lean_object* v_res_1450_; 
v_usedLetOnly_boxed_1445_ = lean_unbox(v_usedLetOnly_1433_);
v_skipConstInApp_boxed_1446_ = lean_unbox(v_skipConstInApp_1434_);
v_skipInstances_boxed_1447_ = lean_unbox(v_skipInstances_1435_);
v_sz_boxed_1448_ = lean_unbox_usize(v_sz_1436_);
lean_dec(v_sz_1436_);
v_i_boxed_1449_ = lean_unbox_usize(v_i_1437_);
lean_dec(v_i_1437_);
v_res_1450_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_pre_1431_, v_post_1432_, v_usedLetOnly_boxed_1445_, v_skipConstInApp_boxed_1446_, v_skipInstances_boxed_1447_, v_sz_boxed_1448_, v_i_boxed_1449_, v_bs_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___boxed(lean_object* v_pre_1451_, lean_object* v_post_1452_, lean_object* v_usedLetOnly_1453_, lean_object* v_skipConstInApp_1454_, lean_object* v_skipInstances_1455_, lean_object* v_e_1456_, lean_object* v_a_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
uint8_t v_usedLetOnly_boxed_1463_; uint8_t v_skipConstInApp_boxed_1464_; uint8_t v_skipInstances_boxed_1465_; lean_object* v_res_1466_; 
v_usedLetOnly_boxed_1463_ = lean_unbox(v_usedLetOnly_1453_);
v_skipConstInApp_boxed_1464_ = lean_unbox(v_skipConstInApp_1454_);
v_skipInstances_boxed_1465_ = lean_unbox(v_skipInstances_1455_);
v_res_1466_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1451_, v_post_1452_, v_usedLetOnly_boxed_1463_, v_skipConstInApp_boxed_1464_, v_skipInstances_boxed_1465_, v_e_1456_, v_a_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v_a_1457_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___boxed(lean_object* v_pre_1467_, lean_object* v_post_1468_, lean_object* v_usedLetOnly_1469_, lean_object* v_skipConstInApp_1470_, lean_object* v_skipInstances_1471_, lean_object* v_fvars_1472_, lean_object* v_e_1473_, lean_object* v_a_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
uint8_t v_usedLetOnly_boxed_1480_; uint8_t v_skipConstInApp_boxed_1481_; uint8_t v_skipInstances_boxed_1482_; lean_object* v_res_1483_; 
v_usedLetOnly_boxed_1480_ = lean_unbox(v_usedLetOnly_1469_);
v_skipConstInApp_boxed_1481_ = lean_unbox(v_skipConstInApp_1470_);
v_skipInstances_boxed_1482_ = lean_unbox(v_skipInstances_1471_);
v_res_1483_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1467_, v_post_1468_, v_usedLetOnly_boxed_1480_, v_skipConstInApp_boxed_1481_, v_skipInstances_boxed_1482_, v_fvars_1472_, v_e_1473_, v_a_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v_a_1474_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___boxed(lean_object* v_pre_1484_, lean_object* v_post_1485_, lean_object* v_usedLetOnly_1486_, lean_object* v_skipConstInApp_1487_, lean_object* v_skipInstances_1488_, lean_object* v_fvars_1489_, lean_object* v_e_1490_, lean_object* v_a_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
uint8_t v_usedLetOnly_boxed_1497_; uint8_t v_skipConstInApp_boxed_1498_; uint8_t v_skipInstances_boxed_1499_; lean_object* v_res_1500_; 
v_usedLetOnly_boxed_1497_ = lean_unbox(v_usedLetOnly_1486_);
v_skipConstInApp_boxed_1498_ = lean_unbox(v_skipConstInApp_1487_);
v_skipInstances_boxed_1499_ = lean_unbox(v_skipInstances_1488_);
v_res_1500_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_1484_, v_post_1485_, v_usedLetOnly_boxed_1497_, v_skipConstInApp_boxed_1498_, v_skipInstances_boxed_1499_, v_fvars_1489_, v_e_1490_, v_a_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v_a_1491_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___boxed(lean_object* v_pre_1501_, lean_object* v_post_1502_, lean_object* v_usedLetOnly_1503_, lean_object* v_skipConstInApp_1504_, lean_object* v_skipInstances_1505_, lean_object* v_fvars_1506_, lean_object* v_e_1507_, lean_object* v_a_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
uint8_t v_usedLetOnly_boxed_1514_; uint8_t v_skipConstInApp_boxed_1515_; uint8_t v_skipInstances_boxed_1516_; lean_object* v_res_1517_; 
v_usedLetOnly_boxed_1514_ = lean_unbox(v_usedLetOnly_1503_);
v_skipConstInApp_boxed_1515_ = lean_unbox(v_skipConstInApp_1504_);
v_skipInstances_boxed_1516_ = lean_unbox(v_skipInstances_1505_);
v_res_1517_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_1501_, v_post_1502_, v_usedLetOnly_boxed_1514_, v_skipConstInApp_boxed_1515_, v_skipInstances_boxed_1516_, v_fvars_1506_, v_e_1507_, v_a_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v_a_1508_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_upperBound_1518_, lean_object* v___x_1519_, lean_object* v_pre_1520_, lean_object* v_post_1521_, lean_object* v_usedLetOnly_1522_, lean_object* v_skipConstInApp_1523_, lean_object* v_skipInstances_1524_, lean_object* v_a_1525_, lean_object* v_b_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
uint8_t v_usedLetOnly_boxed_1533_; uint8_t v_skipConstInApp_boxed_1534_; uint8_t v_skipInstances_boxed_1535_; lean_object* v_res_1536_; 
v_usedLetOnly_boxed_1533_ = lean_unbox(v_usedLetOnly_1522_);
v_skipConstInApp_boxed_1534_ = lean_unbox(v_skipConstInApp_1523_);
v_skipInstances_boxed_1535_ = lean_unbox(v_skipInstances_1524_);
v_res_1536_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v_upperBound_1518_, v___x_1519_, v_pre_1520_, v_post_1521_, v_usedLetOnly_boxed_1533_, v_skipConstInApp_boxed_1534_, v_skipInstances_boxed_1535_, v_a_1525_, v_b_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___x_1519_);
lean_dec(v_upperBound_1518_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8___boxed(lean_object* v_skipInstances_1537_, lean_object* v_pre_1538_, lean_object* v_post_1539_, lean_object* v_usedLetOnly_1540_, lean_object* v_skipConstInApp_1541_, lean_object* v_x_1542_, lean_object* v_x_1543_, lean_object* v_x_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
uint8_t v_skipInstances_boxed_1551_; uint8_t v_usedLetOnly_boxed_1552_; uint8_t v_skipConstInApp_boxed_1553_; lean_object* v_res_1554_; 
v_skipInstances_boxed_1551_ = lean_unbox(v_skipInstances_1537_);
v_usedLetOnly_boxed_1552_ = lean_unbox(v_usedLetOnly_1540_);
v_skipConstInApp_boxed_1553_ = lean_unbox(v_skipConstInApp_1541_);
v_res_1554_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_boxed_1551_, v_pre_1538_, v_post_1539_, v_usedLetOnly_boxed_1552_, v_skipConstInApp_boxed_1553_, v_x_1542_, v_x_1543_, v_x_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
return v_res_1554_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1555_ = lean_box(0);
v___x_1556_ = lean_unsigned_to_nat(16u);
v___x_1557_ = lean_mk_array(v___x_1556_, v___x_1555_);
return v___x_1557_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1558_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0);
v___x_1559_ = lean_unsigned_to_nat(0u);
v___x_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
lean_ctor_set(v___x_1560_, 1, v___x_1558_);
return v___x_1560_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_1562_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1562_, 0, lean_box(0));
lean_closure_set(v___x_1562_, 1, lean_box(0));
lean_closure_set(v___x_1562_, 2, v___x_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(lean_object* v_input_1563_, lean_object* v_pre_1564_, lean_object* v_post_1565_, uint8_t v_usedLetOnly_1566_, uint8_t v_skipConstInApp_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v_a_1575_; uint8_t v___x_1576_; lean_object* v___x_1577_; 
v___x_1573_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
v___x_1574_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v___x_1573_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1575_);
lean_dec_ref(v___x_1574_);
v___x_1576_ = 0;
v___x_1577_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1564_, v_post_1565_, v_usedLetOnly_1566_, v_skipConstInApp_1567_, v___x_1576_, v_input_1563_, v_a_1575_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
v___x_1579_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1579_, 0, lean_box(0));
lean_closure_set(v___x_1579_, 1, lean_box(0));
lean_closure_set(v___x_1579_, 2, v_a_1575_);
v___x_1580_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v___x_1579_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1587_ == 0)
{
lean_object* v_unused_1588_; 
v_unused_1588_ = lean_ctor_get(v___x_1580_, 0);
lean_dec(v_unused_1588_);
v___x_1582_ = v___x_1580_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_dec(v___x_1580_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 0, v_a_1578_);
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1578_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
else
{
lean_dec(v_a_1575_);
return v___x_1577_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___boxed(lean_object* v_input_1589_, lean_object* v_pre_1590_, lean_object* v_post_1591_, lean_object* v_usedLetOnly_1592_, lean_object* v_skipConstInApp_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
uint8_t v_usedLetOnly_boxed_1599_; uint8_t v_skipConstInApp_boxed_1600_; lean_object* v_res_1601_; 
v_usedLetOnly_boxed_1599_ = lean_unbox(v_usedLetOnly_1592_);
v_skipConstInApp_boxed_1600_ = lean_unbox(v_skipConstInApp_1593_);
v_res_1601_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_input_1589_, v_pre_1590_, v_post_1591_, v_usedLetOnly_boxed_1599_, v_skipConstInApp_boxed_1600_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object* v_e_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v___x_1610_; lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1623_; 
v___x_1610_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_1604_, v_a_1608_);
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1613_ = v___x_1610_;
v_isShared_1614_ = v_isSharedCheck_1623_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1623_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
uint8_t v___x_1615_; 
v___x_1615_ = lean_unbox(v_a_1611_);
lean_dec(v_a_1611_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1617_; 
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v_e_1604_);
v___x_1617_ = v___x_1613_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_e_1604_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
else
{
lean_object* v___f_1619_; uint8_t v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_del_object(v___x_1613_);
v___f_1619_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducible___closed__0));
v___x_1620_ = 0;
v___x_1621_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducible___closed__1));
v___x_1622_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_e_1604_, v___x_1621_, v___f_1619_, v___x_1620_, v___x_1620_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
return v___x_1622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___boxed(lean_object* v_e_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Lean_Meta_Sym_unfoldReducible(v_e_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
lean_dec(v_a_1626_);
lean_dec_ref(v_a_1625_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(lean_object* v_upperBound_1631_, lean_object* v___x_1632_, lean_object* v_pre_1633_, lean_object* v_post_1634_, uint8_t v_usedLetOnly_1635_, uint8_t v_skipConstInApp_1636_, uint8_t v_skipInstances_1637_, lean_object* v___x_1638_, lean_object* v_inst_1639_, lean_object* v_R_1640_, lean_object* v_a_1641_, lean_object* v_b_1642_, lean_object* v_c_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v_upperBound_1631_, v___x_1632_, v_pre_1633_, v_post_1634_, v_usedLetOnly_1635_, v_skipConstInApp_1636_, v_skipInstances_1637_, v_a_1641_, v_b_1642_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_1651_ = _args[0];
lean_object* v___x_1652_ = _args[1];
lean_object* v_pre_1653_ = _args[2];
lean_object* v_post_1654_ = _args[3];
lean_object* v_usedLetOnly_1655_ = _args[4];
lean_object* v_skipConstInApp_1656_ = _args[5];
lean_object* v_skipInstances_1657_ = _args[6];
lean_object* v___x_1658_ = _args[7];
lean_object* v_inst_1659_ = _args[8];
lean_object* v_R_1660_ = _args[9];
lean_object* v_a_1661_ = _args[10];
lean_object* v_b_1662_ = _args[11];
lean_object* v_c_1663_ = _args[12];
lean_object* v___y_1664_ = _args[13];
lean_object* v___y_1665_ = _args[14];
lean_object* v___y_1666_ = _args[15];
lean_object* v___y_1667_ = _args[16];
lean_object* v___y_1668_ = _args[17];
lean_object* v___y_1669_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_1670_; uint8_t v_skipConstInApp_boxed_1671_; uint8_t v_skipInstances_boxed_1672_; lean_object* v_res_1673_; 
v_usedLetOnly_boxed_1670_ = lean_unbox(v_usedLetOnly_1655_);
v_skipConstInApp_boxed_1671_ = lean_unbox(v_skipConstInApp_1656_);
v_skipInstances_boxed_1672_ = lean_unbox(v_skipInstances_1657_);
v_res_1673_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_upperBound_1651_, v___x_1652_, v_pre_1653_, v_post_1654_, v_usedLetOnly_boxed_1670_, v_skipConstInApp_boxed_1671_, v_skipInstances_boxed_1672_, v___x_1658_, v_inst_1659_, v_R_1660_, v_a_1661_, v_b_1662_, v_c_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec(v___x_1658_);
lean_dec_ref(v___x_1652_);
lean_dec(v_upperBound_1651_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_1674_, lean_object* v_m_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_m_1675_, v_a_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_1678_, lean_object* v_m_1679_, lean_object* v_a_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(v_00_u03b2_1678_, v_m_1679_, v_a_1680_);
lean_dec_ref(v_a_1680_);
lean_dec_ref(v_m_1679_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1682_, lean_object* v_name_1683_, uint8_t v_bi_1684_, lean_object* v_type_1685_, lean_object* v_k_1686_, uint8_t v_kind_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_1683_, v_bi_1684_, v_type_1685_, v_k_1686_, v_kind_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1695_, lean_object* v_name_1696_, lean_object* v_bi_1697_, lean_object* v_type_1698_, lean_object* v_k_1699_, lean_object* v_kind_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
uint8_t v_bi_boxed_1707_; uint8_t v_kind_boxed_1708_; lean_object* v_res_1709_; 
v_bi_boxed_1707_ = lean_unbox(v_bi_1697_);
v_kind_boxed_1708_ = lean_unbox(v_kind_1700_);
v_res_1709_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1695_, v_name_1696_, v_bi_boxed_1707_, v_type_1698_, v_k_1699_, v_kind_boxed_1708_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(lean_object* v_00_u03b1_1710_, lean_object* v_name_1711_, lean_object* v_type_1712_, lean_object* v_val_1713_, lean_object* v_k_1714_, uint8_t v_nondep_1715_, uint8_t v_kind_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_1711_, v_type_1712_, v_val_1713_, v_k_1714_, v_nondep_1715_, v_kind_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1724_, lean_object* v_name_1725_, lean_object* v_type_1726_, lean_object* v_val_1727_, lean_object* v_k_1728_, lean_object* v_nondep_1729_, lean_object* v_kind_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
uint8_t v_nondep_boxed_1737_; uint8_t v_kind_boxed_1738_; lean_object* v_res_1739_; 
v_nondep_boxed_1737_ = lean_unbox(v_nondep_1729_);
v_kind_boxed_1738_ = lean_unbox(v_kind_1730_);
v_res_1739_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_1724_, v_name_1725_, v_type_1726_, v_val_1727_, v_k_1728_, v_nondep_boxed_1737_, v_kind_boxed_1738_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(lean_object* v_00_u03b1_1740_, lean_object* v_ref_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1741_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___boxed(lean_object* v_00_u03b1_1748_, lean_object* v_ref_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_1748_, v_ref_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(lean_object* v_00_u03b1_1756_, lean_object* v_x_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___boxed(lean_object* v_00_u03b1_1765_, lean_object* v_x_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(v_00_u03b1_1765_, v_x_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10(lean_object* v_00_u03b2_1774_, lean_object* v_m_1775_, lean_object* v_a_1776_, lean_object* v_b_1777_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v_m_1775_, v_a_1776_, v_b_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(lean_object* v_00_u03b2_1779_, lean_object* v_a_1780_, lean_object* v_x_1781_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1780_, v_x_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_00_u03b2_1783_, lean_object* v_a_1784_, lean_object* v_x_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_1783_, v_a_1784_, v_x_1785_);
lean_dec(v_x_1785_);
lean_dec_ref(v_a_1784_);
return v_res_1786_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(lean_object* v_00_u03b2_1787_, lean_object* v_a_1788_, lean_object* v_x_1789_){
_start:
{
uint8_t v___x_1790_; 
v___x_1790_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_1788_, v_x_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___boxed(lean_object* v_00_u03b2_1791_, lean_object* v_a_1792_, lean_object* v_x_1793_){
_start:
{
uint8_t v_res_1794_; lean_object* v_r_1795_; 
v_res_1794_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_1791_, v_a_1792_, v_x_1793_);
lean_dec(v_x_1793_);
lean_dec_ref(v_a_1792_);
v_r_1795_ = lean_box(v_res_1794_);
return v_r_1795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16(lean_object* v_00_u03b2_1796_, lean_object* v_data_1797_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(v_data_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17(lean_object* v_00_u03b2_1799_, lean_object* v_a_1800_, lean_object* v_b_1801_, lean_object* v_x_1802_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_1800_, v_b_1801_, v_x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object* v_00_u03b2_1804_, lean_object* v_i_1805_, lean_object* v_source_1806_, lean_object* v_target_1807_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_1805_, v_source_1806_, v_target_1807_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object* v_00_u03b2_1809_, lean_object* v_x_1810_, lean_object* v_x_1811_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_1810_, v_x_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0(lean_object* v_x_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___boxed(lean_object* v_x_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_Meta_Sym_foldProjs___lam__0(v_x_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec_ref(v_x_1821_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(lean_object* v_msgData_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v___x_1834_; lean_object* v_env_1835_; lean_object* v___x_1836_; lean_object* v_mctx_1837_; lean_object* v_lctx_1838_; lean_object* v_options_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1834_ = lean_st_ref_get(v___y_1832_);
v_env_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc_ref(v_env_1835_);
lean_dec(v___x_1834_);
v___x_1836_ = lean_st_ref_get(v___y_1830_);
v_mctx_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc_ref(v_mctx_1837_);
lean_dec(v___x_1836_);
v_lctx_1838_ = lean_ctor_get(v___y_1829_, 2);
v_options_1839_ = lean_ctor_get(v___y_1831_, 1);
lean_inc_ref(v_options_1839_);
lean_inc_ref(v_lctx_1838_);
v___x_1840_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1840_, 0, v_env_1835_);
lean_ctor_set(v___x_1840_, 1, v_mctx_1837_);
lean_ctor_set(v___x_1840_, 2, v_lctx_1838_);
lean_ctor_set(v___x_1840_, 3, v_options_1839_);
v___x_1841_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
lean_ctor_set(v___x_1841_, 1, v_msgData_1828_);
v___x_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0___boxed(lean_object* v_msgData_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msgData_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
return v_res_1849_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1850_; double v___x_1851_; 
v___x_1850_ = lean_unsigned_to_nat(0u);
v___x_1851_ = lean_float_of_nat(v___x_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(lean_object* v_cls_1855_, lean_object* v_msg_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_ref_1862_; lean_object* v___x_1863_; lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1908_; 
v_ref_1862_ = lean_ctor_get(v___y_1859_, 4);
v___x_1863_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1866_ = v___x_1863_;
v_isShared_1867_ = v_isSharedCheck_1908_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1863_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1908_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1868_; lean_object* v_traceState_1869_; lean_object* v_env_1870_; lean_object* v_nextMacroScope_1871_; lean_object* v_ngen_1872_; lean_object* v_auxDeclNGen_1873_; lean_object* v_cache_1874_; lean_object* v_messages_1875_; lean_object* v_infoState_1876_; lean_object* v_snapshotTasks_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1907_; 
v___x_1868_ = lean_st_ref_take(v___y_1860_);
v_traceState_1869_ = lean_ctor_get(v___x_1868_, 4);
v_env_1870_ = lean_ctor_get(v___x_1868_, 0);
v_nextMacroScope_1871_ = lean_ctor_get(v___x_1868_, 1);
v_ngen_1872_ = lean_ctor_get(v___x_1868_, 2);
v_auxDeclNGen_1873_ = lean_ctor_get(v___x_1868_, 3);
v_cache_1874_ = lean_ctor_get(v___x_1868_, 5);
v_messages_1875_ = lean_ctor_get(v___x_1868_, 6);
v_infoState_1876_ = lean_ctor_get(v___x_1868_, 7);
v_snapshotTasks_1877_ = lean_ctor_get(v___x_1868_, 8);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1879_ = v___x_1868_;
v_isShared_1880_ = v_isSharedCheck_1907_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_snapshotTasks_1877_);
lean_inc(v_infoState_1876_);
lean_inc(v_messages_1875_);
lean_inc(v_cache_1874_);
lean_inc(v_traceState_1869_);
lean_inc(v_auxDeclNGen_1873_);
lean_inc(v_ngen_1872_);
lean_inc(v_nextMacroScope_1871_);
lean_inc(v_env_1870_);
lean_dec(v___x_1868_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1907_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
uint64_t v_tid_1881_; lean_object* v_traces_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1906_; 
v_tid_1881_ = lean_ctor_get_uint64(v_traceState_1869_, sizeof(void*)*1);
v_traces_1882_ = lean_ctor_get(v_traceState_1869_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v_traceState_1869_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1884_ = v_traceState_1869_;
v_isShared_1885_ = v_isSharedCheck_1906_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_traces_1882_);
lean_dec(v_traceState_1869_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1906_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; double v___x_1887_; uint8_t v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1886_ = lean_box(0);
v___x_1887_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_1888_ = 0;
v___x_1889_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_1890_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1890_, 0, v_cls_1855_);
lean_ctor_set(v___x_1890_, 1, v___x_1886_);
lean_ctor_set(v___x_1890_, 2, v___x_1889_);
lean_ctor_set_float(v___x_1890_, sizeof(void*)*3, v___x_1887_);
lean_ctor_set_float(v___x_1890_, sizeof(void*)*3 + 8, v___x_1887_);
lean_ctor_set_uint8(v___x_1890_, sizeof(void*)*3 + 16, v___x_1888_);
v___x_1891_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
v___x_1892_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1890_);
lean_ctor_set(v___x_1892_, 1, v_a_1864_);
lean_ctor_set(v___x_1892_, 2, v___x_1891_);
lean_inc(v_ref_1862_);
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v_ref_1862_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
v___x_1894_ = l_Lean_PersistentArray_push___redArg(v_traces_1882_, v___x_1893_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 0, v___x_1894_);
v___x_1896_ = v___x_1884_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1894_);
lean_ctor_set_uint64(v_reuseFailAlloc_1905_, sizeof(void*)*1, v_tid_1881_);
v___x_1896_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1898_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 4, v___x_1896_);
v___x_1898_ = v___x_1879_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_env_1870_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_nextMacroScope_1871_);
lean_ctor_set(v_reuseFailAlloc_1904_, 2, v_ngen_1872_);
lean_ctor_set(v_reuseFailAlloc_1904_, 3, v_auxDeclNGen_1873_);
lean_ctor_set(v_reuseFailAlloc_1904_, 4, v___x_1896_);
lean_ctor_set(v_reuseFailAlloc_1904_, 5, v_cache_1874_);
lean_ctor_set(v_reuseFailAlloc_1904_, 6, v_messages_1875_);
lean_ctor_set(v_reuseFailAlloc_1904_, 7, v_infoState_1876_);
lean_ctor_set(v_reuseFailAlloc_1904_, 8, v_snapshotTasks_1877_);
v___x_1898_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1902_; 
v___x_1899_ = lean_st_ref_put(v___y_1860_, v___x_1898_);
v___x_1900_ = lean_box(0);
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 0, v___x_1900_);
v___x_1902_ = v___x_1866_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1900_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___boxed(lean_object* v_cls_1909_, lean_object* v_msg_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v_cls_1909_, v_msg_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
return v_res_1916_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1920_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_1921_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__1));
v___x_1922_ = l_Lean_Name_append(v___x_1921_, v___x_1920_);
return v___x_1922_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__3));
v___x_1925_ = l_Lean_stringToMessageData(v___x_1924_);
return v___x_1925_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__5));
v___x_1928_ = l_Lean_stringToMessageData(v___x_1927_);
return v___x_1928_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__8(void){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__7));
v___x_1931_ = l_Lean_stringToMessageData(v___x_1930_);
return v___x_1931_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__10(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__9));
v___x_1934_ = l_Lean_stringToMessageData(v___x_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1(lean_object* v_e_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v___y_1945_; 
if (lean_obj_tag(v_e_1935_) == 11)
{
lean_object* v_typeName_1966_; lean_object* v_idx_1967_; lean_object* v_struct_1968_; lean_object* v___x_1969_; lean_object* v_env_1970_; lean_object* v___x_1971_; 
v_typeName_1966_ = lean_ctor_get(v_e_1935_, 0);
v_idx_1967_ = lean_ctor_get(v_e_1935_, 1);
v_struct_1968_ = lean_ctor_get(v_e_1935_, 2);
v___x_1969_ = lean_st_ref_get(v___y_1939_);
v_env_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc_ref(v_env_1970_);
lean_dec(v___x_1969_);
lean_inc(v_typeName_1966_);
v___x_1971_ = l_Lean_getStructureInfo_x3f(v_env_1970_, v_typeName_1966_);
if (lean_obj_tag(v___x_1971_) == 1)
{
lean_object* v_val_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_2026_; 
v_val_1972_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_1974_ = v___x_1971_;
v_isShared_1975_ = v_isSharedCheck_2026_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_val_1972_);
lean_dec(v___x_1971_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_2026_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v_fieldNames_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
v_fieldNames_1976_ = lean_ctor_get(v_val_1972_, 1);
lean_inc_ref(v_fieldNames_1976_);
lean_dec(v_val_1972_);
v___x_1977_ = lean_array_get_size(v_fieldNames_1976_);
v___x_1978_ = lean_nat_dec_lt(v_idx_1967_, v___x_1977_);
if (v___x_1978_ == 0)
{
lean_object* v_options_1979_; uint8_t v_hasTrace_1980_; 
lean_dec_ref(v_fieldNames_1976_);
v_options_1979_ = lean_ctor_get(v___y_1938_, 1);
v_hasTrace_1980_ = lean_ctor_get_uint8(v_options_1979_, sizeof(void*)*1);
if (v_hasTrace_1980_ == 0)
{
lean_del_object(v___x_1974_);
goto v___jp_1941_;
}
else
{
lean_object* v_toCold_1981_; lean_object* v_inheritedTraceOptions_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; 
v_toCold_1981_ = lean_ctor_get(v___y_1938_, 0);
v_inheritedTraceOptions_1982_ = lean_ctor_get(v_toCold_1981_, 4);
v___x_1983_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_1984_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__2);
v___x_1985_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1982_, v_options_1979_, v___x_1984_);
if (v___x_1985_ == 0)
{
lean_del_object(v___x_1974_);
goto v___jp_1941_;
}
else
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1989_; 
v___x_1986_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__4, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__4_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__4);
lean_inc(v_idx_1967_);
v___x_1987_ = l_Nat_reprFast(v_idx_1967_);
if (v_isShared_1975_ == 0)
{
lean_ctor_set_tag(v___x_1974_, 3);
lean_ctor_set(v___x_1974_, 0, v___x_1987_);
v___x_1989_ = v___x_1974_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_2005_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1990_ = l_Lean_MessageData_ofFormat(v___x_1989_);
v___x_1991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1986_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__6, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__6_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__6);
v___x_1993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1991_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
lean_inc_ref(v_e_1935_);
v___x_1994_ = l_Lean_indentExpr(v_e_1935_);
v___x_1995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1993_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___x_1996_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v___x_1983_, v___x_1995_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_dec_ref_known(v___x_1996_, 1);
goto v___jp_1941_;
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_dec_ref_known(v_e_1935_, 3);
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1996_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1996_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2006_; uint8_t v_transparency_2007_; lean_object* v___x_2008_; uint8_t v___x_2009_; uint8_t v___x_2010_; 
lean_inc_ref(v_struct_1968_);
lean_inc(v_idx_1967_);
lean_del_object(v___x_1974_);
lean_dec_ref_known(v_e_1935_, 3);
v___x_2006_ = l_Lean_Meta_Context_config(v___y_1936_);
v_transparency_2007_ = lean_ctor_get_uint8(v___x_2006_, 9);
lean_dec_ref(v___x_2006_);
v___x_2008_ = lean_array_fget(v_fieldNames_1976_, v_idx_1967_);
lean_dec(v_idx_1967_);
lean_dec_ref(v_fieldNames_1976_);
v___x_2009_ = 1;
v___x_2010_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2007_, v___x_2009_);
if (v___x_2010_ == 0)
{
lean_object* v_keyedConfig_2011_; uint8_t v_trackZetaDelta_2012_; lean_object* v_zetaDeltaSet_2013_; lean_object* v_lctx_2014_; lean_object* v_localInstances_2015_; lean_object* v_defEqCtx_x3f_2016_; lean_object* v_synthPendingDepth_2017_; lean_object* v_customCanUnfoldPredicate_x3f_2018_; uint8_t v_univApprox_2019_; uint8_t v_inTypeClassResolution_2020_; uint8_t v_cacheInferType_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v_keyedConfig_2011_ = lean_ctor_get(v___y_1936_, 0);
v_trackZetaDelta_2012_ = lean_ctor_get_uint8(v___y_1936_, sizeof(void*)*7);
v_zetaDeltaSet_2013_ = lean_ctor_get(v___y_1936_, 1);
v_lctx_2014_ = lean_ctor_get(v___y_1936_, 2);
v_localInstances_2015_ = lean_ctor_get(v___y_1936_, 3);
v_defEqCtx_x3f_2016_ = lean_ctor_get(v___y_1936_, 4);
v_synthPendingDepth_2017_ = lean_ctor_get(v___y_1936_, 5);
v_customCanUnfoldPredicate_x3f_2018_ = lean_ctor_get(v___y_1936_, 6);
v_univApprox_2019_ = lean_ctor_get_uint8(v___y_1936_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2020_ = lean_ctor_get_uint8(v___y_1936_, sizeof(void*)*7 + 2);
v_cacheInferType_2021_ = lean_ctor_get_uint8(v___y_1936_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2011_);
v___x_2022_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2009_, v_keyedConfig_2011_);
lean_inc(v_customCanUnfoldPredicate_x3f_2018_);
lean_inc(v_synthPendingDepth_2017_);
lean_inc(v_defEqCtx_x3f_2016_);
lean_inc_ref(v_localInstances_2015_);
lean_inc_ref(v_lctx_2014_);
lean_inc(v_zetaDeltaSet_2013_);
v___x_2023_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
lean_ctor_set(v___x_2023_, 1, v_zetaDeltaSet_2013_);
lean_ctor_set(v___x_2023_, 2, v_lctx_2014_);
lean_ctor_set(v___x_2023_, 3, v_localInstances_2015_);
lean_ctor_set(v___x_2023_, 4, v_defEqCtx_x3f_2016_);
lean_ctor_set(v___x_2023_, 5, v_synthPendingDepth_2017_);
lean_ctor_set(v___x_2023_, 6, v_customCanUnfoldPredicate_x3f_2018_);
lean_ctor_set_uint8(v___x_2023_, sizeof(void*)*7, v_trackZetaDelta_2012_);
lean_ctor_set_uint8(v___x_2023_, sizeof(void*)*7 + 1, v_univApprox_2019_);
lean_ctor_set_uint8(v___x_2023_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2020_);
lean_ctor_set_uint8(v___x_2023_, sizeof(void*)*7 + 3, v_cacheInferType_2021_);
v___x_2024_ = l_Lean_Meta_mkProjection(v_struct_1968_, v___x_2008_, v___x_2023_, v___y_1937_, v___y_1938_, v___y_1939_);
lean_dec_ref_known(v___x_2023_, 7);
v___y_1945_ = v___x_2024_;
goto v___jp_1944_;
}
else
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Lean_Meta_mkProjection(v_struct_1968_, v___x_2008_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
v___y_1945_ = v___x_2025_;
goto v___jp_1944_;
}
}
}
}
else
{
lean_object* v_options_2027_; uint8_t v_hasTrace_2028_; 
lean_dec(v___x_1971_);
v_options_2027_ = lean_ctor_get(v___y_1938_, 1);
v_hasTrace_2028_ = lean_ctor_get_uint8(v_options_2027_, sizeof(void*)*1);
if (v_hasTrace_2028_ == 0)
{
goto v___jp_1963_;
}
else
{
lean_object* v_toCold_2029_; lean_object* v_inheritedTraceOptions_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v_toCold_2029_ = lean_ctor_get(v___y_1938_, 0);
v_inheritedTraceOptions_2030_ = lean_ctor_get(v_toCold_2029_, 4);
v___x_2031_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_2032_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__2);
v___x_2033_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2030_, v_options_2027_, v___x_2032_);
if (v___x_2033_ == 0)
{
goto v___jp_1963_;
}
else
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2034_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__8, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__8_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__8);
lean_inc(v_typeName_1966_);
v___x_2035_ = l_Lean_MessageData_ofName(v_typeName_1966_);
v___x_2036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2034_);
lean_ctor_set(v___x_2036_, 1, v___x_2035_);
v___x_2037_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__10, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__10_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__10);
v___x_2038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2036_);
lean_ctor_set(v___x_2038_, 1, v___x_2037_);
lean_inc_ref(v_e_1935_);
v___x_2039_ = l_Lean_indentExpr(v_e_1935_);
v___x_2040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2038_);
lean_ctor_set(v___x_2040_, 1, v___x_2039_);
v___x_2041_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v___x_2031_, v___x_2040_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_dec_ref_known(v___x_2041_, 1);
goto v___jp_1963_;
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec_ref_known(v_e_1935_, 3);
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
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
}
}
}
else
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2050_, 0, v_e_1935_);
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
return v___x_2051_;
}
v___jp_1941_:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1942_, 0, v_e_1935_);
v___x_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
return v___x_1943_;
}
v___jp_1944_:
{
if (lean_obj_tag(v___y_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1954_; 
v_a_1946_ = lean_ctor_get(v___y_1945_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___y_1945_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1948_ = v___y_1945_;
v_isShared_1949_ = v_isSharedCheck_1954_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___y_1945_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1954_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1950_; lean_object* v___x_1952_; 
v___x_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1950_, 0, v_a_1946_);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v___x_1950_);
v___x_1952_ = v___x_1948_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1950_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
v_a_1955_ = lean_ctor_get(v___y_1945_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___y_1945_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___y_1945_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___y_1945_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
v___jp_1963_:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1964_, 0, v_e_1935_);
v___x_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1964_);
return v___x_1965_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___boxed(lean_object* v_e_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Lean_Meta_Sym_foldProjs___lam__1(v_e_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs(lean_object* v_e_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_){
_start:
{
lean_object* v___f_2068_; lean_object* v___x_2069_; 
v___f_2068_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__0));
v___x_2069_ = lean_find_expr(v___f_2068_, v_e_2062_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v___x_2070_; 
v___x_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2070_, 0, v_e_2062_);
return v___x_2070_;
}
else
{
lean_object* v___f_2071_; lean_object* v_post_2072_; uint8_t v___x_2073_; lean_object* v___x_2074_; 
lean_dec_ref_known(v___x_2069_, 1);
v___f_2071_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__1));
v_post_2072_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__2));
v___x_2073_ = 0;
v___x_2074_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_e_2062_, v___f_2071_, v_post_2072_, v___x_2073_, v___x_2073_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_);
return v___x_2074_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___boxed(lean_object* v_e_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Lean_Meta_Sym_foldProjs(v_e_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
return v_res_2081_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2085_ = lean_box(0);
v___x_2086_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1));
v___x_2087_ = l_Lean_mkConst(v___x_2086_, v___x_2085_);
return v___x_2087_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = lean_box(0);
v___x_2092_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4));
v___x_2093_ = l_Lean_mkConst(v___x_2092_, v___x_2091_);
return v___x_2093_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9(void){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2099_ = lean_box(0);
v___x_2100_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8));
v___x_2101_ = l_Lean_mkConst(v___x_2100_, v___x_2099_);
return v___x_2101_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12(void){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2106_ = lean_box(0);
v___x_2107_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11));
v___x_2108_ = l_Lean_mkConst(v___x_2107_, v___x_2106_);
return v___x_2108_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13(void){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = lean_unsigned_to_nat(0u);
v___x_2110_ = l_Lean_mkNatLit(v___x_2109_);
return v___x_2110_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17(void){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2116_ = lean_box(0);
v___x_2117_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16));
v___x_2118_ = l_Lean_mkConst(v___x_2117_, v___x_2116_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2);
v___x_2122_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2121_, v_a_2119_, v_a_2120_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v_a_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
v_a_2124_ = lean_ctor_get(v___x_2122_, 1);
lean_inc(v_a_2124_);
lean_dec_ref_known(v___x_2122_, 2);
v___x_2125_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5);
v___x_2126_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2125_, v_a_2119_, v_a_2124_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v_a_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
v_a_2128_ = lean_ctor_get(v___x_2126_, 1);
lean_inc(v_a_2128_);
lean_dec_ref_known(v___x_2126_, 2);
v___x_2129_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9);
v___x_2130_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2129_, v_a_2119_, v_a_2128_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v_a_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
v_a_2132_ = lean_ctor_get(v___x_2130_, 1);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2130_, 2);
v___x_2133_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12);
v___x_2134_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2133_, v_a_2119_, v_a_2132_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v_a_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
v_a_2136_ = lean_ctor_get(v___x_2134_, 1);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2134_, 2);
v___x_2137_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13);
v___x_2138_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2137_, v_a_2119_, v_a_2136_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v_a_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
v_a_2140_ = lean_ctor_get(v___x_2138_, 1);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2138_, 2);
v___x_2141_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17);
v___x_2142_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2141_, v_a_2119_, v_a_2140_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v_a_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
v_a_2144_ = lean_ctor_get(v___x_2142_, 1);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2142_, 2);
v___x_2145_ = l_Lean_Int_mkType;
v___x_2146_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2145_, v_a_2119_, v_a_2144_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2156_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
v_a_2148_ = lean_ctor_get(v___x_2146_, 1);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2150_ = v___x_2146_;
v_isShared_2151_ = v_isSharedCheck_2156_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_inc(v_a_2147_);
lean_dec(v___x_2146_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2156_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2152_; lean_object* v___x_2154_; 
v___x_2152_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2152_, 0, v_a_2127_);
lean_ctor_set(v___x_2152_, 1, v_a_2123_);
lean_ctor_set(v___x_2152_, 2, v_a_2139_);
lean_ctor_set(v___x_2152_, 3, v_a_2135_);
lean_ctor_set(v___x_2152_, 4, v_a_2131_);
lean_ctor_set(v___x_2152_, 5, v_a_2143_);
lean_ctor_set(v___x_2152_, 6, v_a_2147_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 0, v___x_2152_);
v___x_2154_ = v___x_2150_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_a_2148_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
else
{
lean_object* v_a_2157_; lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_dec(v_a_2143_);
lean_dec(v_a_2139_);
lean_dec(v_a_2135_);
lean_dec(v_a_2131_);
lean_dec(v_a_2127_);
lean_dec(v_a_2123_);
v_a_2157_ = lean_ctor_get(v___x_2146_, 0);
v_a_2158_ = lean_ctor_get(v___x_2146_, 1);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2146_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_inc(v_a_2157_);
lean_dec(v___x_2146_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2157_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_a_2158_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
else
{
lean_object* v_a_2166_; lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec(v_a_2139_);
lean_dec(v_a_2135_);
lean_dec(v_a_2131_);
lean_dec(v_a_2127_);
lean_dec(v_a_2123_);
v_a_2166_ = lean_ctor_get(v___x_2142_, 0);
v_a_2167_ = lean_ctor_get(v___x_2142_, 1);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2142_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_inc(v_a_2166_);
lean_dec(v___x_2142_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2166_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
else
{
lean_object* v_a_2175_; lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_dec(v_a_2135_);
lean_dec(v_a_2131_);
lean_dec(v_a_2127_);
lean_dec(v_a_2123_);
v_a_2175_ = lean_ctor_get(v___x_2138_, 0);
v_a_2176_ = lean_ctor_get(v___x_2138_, 1);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2138_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_inc(v_a_2175_);
lean_dec(v___x_2138_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2175_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_dec(v_a_2131_);
lean_dec(v_a_2127_);
lean_dec(v_a_2123_);
v_a_2184_ = lean_ctor_get(v___x_2134_, 0);
v_a_2185_ = lean_ctor_get(v___x_2134_, 1);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2134_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_inc(v_a_2184_);
lean_dec(v___x_2134_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2184_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
else
{
lean_object* v_a_2193_; lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_dec(v_a_2127_);
lean_dec(v_a_2123_);
v_a_2193_ = lean_ctor_get(v___x_2130_, 0);
v_a_2194_ = lean_ctor_get(v___x_2130_, 1);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2130_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_inc(v_a_2193_);
lean_dec(v___x_2130_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2193_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
else
{
lean_object* v_a_2202_; lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
lean_dec(v_a_2123_);
v_a_2202_ = lean_ctor_get(v___x_2126_, 0);
v_a_2203_ = lean_ctor_get(v___x_2126_, 1);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v___x_2126_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_inc(v_a_2202_);
lean_dec(v___x_2126_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2202_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_a_2203_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
else
{
lean_object* v_a_2211_; lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
v_a_2211_ = lean_ctor_get(v___x_2122_, 0);
v_a_2212_ = lean_ctor_get(v___x_2122_, 1);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2122_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_inc(v_a_2211_);
lean_dec(v___x_2122_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2211_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___boxed(lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(v_a_2220_, v_a_2221_);
lean_dec_ref(v_a_2220_);
return v_res_2222_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(lean_object* v_opts_2223_, lean_object* v_opt_2224_){
_start:
{
lean_object* v_name_2225_; lean_object* v_defValue_2226_; lean_object* v_map_2227_; lean_object* v___x_2228_; 
v_name_2225_ = lean_ctor_get(v_opt_2224_, 0);
v_defValue_2226_ = lean_ctor_get(v_opt_2224_, 1);
v_map_2227_ = lean_ctor_get(v_opts_2223_, 0);
v___x_2228_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2227_, v_name_2225_);
if (lean_obj_tag(v___x_2228_) == 0)
{
uint8_t v___x_2229_; 
v___x_2229_ = lean_unbox(v_defValue_2226_);
return v___x_2229_;
}
else
{
lean_object* v_val_2230_; 
v_val_2230_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_val_2230_);
lean_dec_ref_known(v___x_2228_, 1);
if (lean_obj_tag(v_val_2230_) == 1)
{
uint8_t v_v_2231_; 
v_v_2231_ = lean_ctor_get_uint8(v_val_2230_, 0);
lean_dec_ref_known(v_val_2230_, 0);
return v_v_2231_;
}
else
{
uint8_t v___x_2232_; 
lean_dec(v_val_2230_);
v___x_2232_ = lean_unbox(v_defValue_2226_);
return v___x_2232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0___boxed(lean_object* v_opts_2233_, lean_object* v_opt_2234_){
_start:
{
uint8_t v_res_2235_; lean_object* v_r_2236_; 
v_res_2235_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(v_opts_2233_, v_opt_2234_);
lean_dec_ref(v_opt_2234_);
lean_dec_ref(v_opts_2233_);
v_r_2236_ = lean_box(v_res_2235_);
return v_r_2236_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2237_; 
v___x_2237_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2237_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0);
v___x_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1(lean_object* v_00_u03b2_2240_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__1);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(lean_object* v_msg_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v___f_2249_; lean_object* v___x_2122__overap_2250_; lean_object* v___x_2251_; 
v___f_2249_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___closed__0));
v___x_2122__overap_2250_ = lean_panic_fn_borrowed(v___f_2249_, v_msg_2243_);
lean_inc(v___y_2247_);
lean_inc_ref(v___y_2246_);
lean_inc(v___y_2245_);
lean_inc_ref(v___y_2244_);
v___x_2251_ = lean_apply_5(v___x_2122__overap_2250_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, lean_box(0));
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___boxed(lean_object* v_msg_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(v_msg_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
return v_res_2258_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2259_; 
v___x_2259_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2259_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__0, &l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0);
v___x_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
return v___x_2261_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2262_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
return v___x_2263_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_2264_; 
v___x_2264_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1(lean_box(0));
return v___x_2264_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__7(void){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2268_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__6));
v___x_2269_ = lean_unsigned_to_nat(19u);
v___x_2270_ = lean_unsigned_to_nat(304u);
v___x_2271_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__5));
v___x_2272_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__4));
v___x_2273_ = l_mkPanicMessageWithDecl(v___x_2272_, v___x_2271_, v___x_2270_, v___x_2269_, v___x_2268_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object* v_x_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_){
_start:
{
lean_object* v_fst_2281_; lean_object* v_snd_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v___x_2322_; lean_object* v_env_2323_; uint8_t v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2322_ = lean_st_ref_get(v_a_2278_);
v_env_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc_ref(v_env_2323_);
lean_dec(v___x_2322_);
v___x_2324_ = 0;
v___x_2325_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2325_, 0, v_env_2323_);
lean_ctor_set_uint8(v___x_2325_, sizeof(void*)*1, v___x_2324_);
lean_ctor_set_uint8(v___x_2325_, sizeof(void*)*1 + 1, v___x_2324_);
v___x_2326_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__3, &l_Lean_Meta_Sym_SymM_run___redArg___closed__3_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__3);
v___x_2327_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(v___x_2325_, v___x_2326_);
lean_dec_ref_known(v___x_2325_, 1);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v_a_2329_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2328_);
v_a_2329_ = lean_ctor_get(v___x_2327_, 1);
lean_inc(v_a_2329_);
lean_dec_ref_known(v___x_2327_, 2);
v_fst_2281_ = v_a_2328_;
v_snd_2282_ = v_a_2329_;
v___y_2283_ = v_a_2275_;
v___y_2284_ = v_a_2276_;
v___y_2285_ = v_a_2277_;
v___y_2286_ = v_a_2278_;
goto v___jp_2280_;
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
lean_dec_ref_known(v___x_2327_, 2);
v___x_2330_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__7, &l_Lean_Meta_Sym_SymM_run___redArg___closed__7_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__7);
v___x_2331_ = l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(v___x_2330_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v_fst_2333_; lean_object* v_snd_2334_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref_known(v___x_2331_, 1);
v_fst_2333_ = lean_ctor_get(v_a_2332_, 0);
lean_inc(v_fst_2333_);
v_snd_2334_ = lean_ctor_get(v_a_2332_, 1);
lean_inc(v_snd_2334_);
lean_dec(v_a_2332_);
v_fst_2281_ = v_fst_2333_;
v_snd_2282_ = v_snd_2334_;
v___y_2283_ = v_a_2275_;
v___y_2284_ = v_a_2276_;
v___y_2285_ = v_a_2277_;
v___y_2286_ = v_a_2278_;
goto v___jp_2280_;
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec_ref(v_x_2274_);
v_a_2335_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2331_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2331_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
v___jp_2280_:
{
lean_object* v___x_2287_; 
v___x_2287_ = l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v_options_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref_known(v___x_2287_, 1);
v_options_2289_ = lean_ctor_get(v___y_2285_, 1);
v___x_2290_ = l_Lean_Meta_Sym_sym_debug;
v___x_2291_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(v_options_2289_, v___x_2290_);
v___x_2292_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedConfig_default___closed__0));
v___x_2293_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__1, &l_Lean_Meta_Sym_SymM_run___redArg___closed__1_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1);
v___x_2294_ = lean_box(0);
v___x_2295_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__2, &l_Lean_Meta_Sym_SymM_run___redArg___closed__2_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__2);
v___x_2296_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v___x_2296_, 0, v_snd_2282_);
lean_ctor_set(v___x_2296_, 1, v___x_2293_);
lean_ctor_set(v___x_2296_, 2, v___x_2293_);
lean_ctor_set(v___x_2296_, 3, v___x_2293_);
lean_ctor_set(v___x_2296_, 4, v___x_2293_);
lean_ctor_set(v___x_2296_, 5, v___x_2293_);
lean_ctor_set(v___x_2296_, 6, v___x_2293_);
lean_ctor_set(v___x_2296_, 7, v_a_2288_);
lean_ctor_set(v___x_2296_, 8, v___x_2294_);
lean_ctor_set(v___x_2296_, 9, v___x_2295_);
lean_ctor_set(v___x_2296_, 10, v___x_2293_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*11, v___x_2291_);
v___x_2297_ = lean_st_mk_ref(v___x_2296_);
v___x_2298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2298_, 0, v_fst_2281_);
lean_ctor_set(v___x_2298_, 1, v___x_2292_);
lean_inc(v___y_2286_);
lean_inc_ref(v___y_2285_);
lean_inc(v___y_2284_);
lean_inc_ref(v___y_2283_);
lean_inc(v___x_2297_);
v___x_2299_ = lean_apply_7(v_x_2274_, v___x_2298_, v___x_2297_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, lean_box(0));
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2308_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2302_ = v___x_2299_;
v_isShared_2303_ = v_isSharedCheck_2308_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2299_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2308_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2304_; lean_object* v___x_2306_; 
v___x_2304_ = lean_st_ref_get(v___x_2297_);
lean_dec(v___x_2297_);
lean_dec(v___x_2304_);
if (v_isShared_2303_ == 0)
{
v___x_2306_ = v___x_2302_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2300_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
else
{
lean_dec(v___x_2297_);
return v___x_2299_;
}
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2321_; 
lean_dec_ref(v_snd_2282_);
lean_dec_ref(v_fst_2281_);
lean_dec_ref(v_x_2274_);
v_a_2309_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2311_ = v___x_2287_;
v_isShared_2312_ = v_isSharedCheck_2321_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2287_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2321_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v_ref_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2319_; 
v_ref_2313_ = lean_ctor_get(v___y_2285_, 4);
v___x_2314_ = lean_io_error_to_string(v_a_2309_);
v___x_2315_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
v___x_2316_ = l_Lean_MessageData_ofFormat(v___x_2315_);
lean_inc(v_ref_2313_);
v___x_2317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2317_, 0, v_ref_2313_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 0, v___x_2317_);
v___x_2319_ = v___x_2311_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg___boxed(lean_object* v_x_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run(lean_object* v_00_u03b1_2350_, lean_object* v_x_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_){
_start:
{
lean_object* v___x_2357_; 
v___x_2357_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___boxed(lean_object* v_00_u03b1_2358_, lean_object* v_x_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_Meta_Sym_SymM_run(v_00_u03b1_2358_, v_x_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
lean_dec(v_a_2363_);
lean_dec_ref(v_a_2362_);
lean_dec(v_a_2361_);
lean_dec_ref(v_a_2360_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg(lean_object* v_a_2366_){
_start:
{
lean_object* v_sharedExprs_2368_; lean_object* v___x_2369_; 
v_sharedExprs_2368_ = lean_ctor_get(v_a_2366_, 0);
lean_inc_ref(v_sharedExprs_2368_);
v___x_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2369_, 0, v_sharedExprs_2368_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg___boxed(lean_object* v_a_2370_, lean_object* v_a_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2370_);
lean_dec_ref(v_a_2370_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs(lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2373_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___boxed(lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lean_Meta_Sym_getSharedExprs(v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object* v_a_2389_){
_start:
{
lean_object* v___x_2391_; lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2400_; 
v___x_2391_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2389_);
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2394_ = v___x_2391_;
v_isShared_2395_ = v_isSharedCheck_2400_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2391_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2400_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v_trueExpr_2396_; lean_object* v___x_2398_; 
v_trueExpr_2396_ = lean_ctor_get(v_a_2392_, 0);
lean_inc_ref(v_trueExpr_2396_);
lean_dec(v_a_2392_);
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 0, v_trueExpr_2396_);
v___x_2398_ = v___x_2394_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_trueExpr_2396_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg___boxed(lean_object* v_a_2401_, lean_object* v_a_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2401_);
lean_dec_ref(v_a_2401_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr(lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2404_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___boxed(lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Lean_Meta_Sym_getTrueExpr(v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
lean_dec(v_a_2417_);
lean_dec_ref(v_a_2416_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
lean_dec(v_a_2413_);
lean_dec_ref(v_a_2412_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object* v_e_2420_, lean_object* v_a_2421_){
_start:
{
lean_object* v___x_2423_; 
v___x_2423_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2421_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2435_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2426_ = v___x_2423_;
v_isShared_2427_ = v_isSharedCheck_2435_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2423_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2435_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
size_t v___x_2428_; size_t v___x_2429_; uint8_t v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2433_; 
v___x_2428_ = lean_ptr_addr(v_e_2420_);
v___x_2429_ = lean_ptr_addr(v_a_2424_);
lean_dec(v_a_2424_);
v___x_2430_ = lean_usize_dec_eq(v___x_2428_, v___x_2429_);
v___x_2431_ = lean_box(v___x_2430_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v___x_2431_);
v___x_2433_ = v___x_2426_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
v_a_2436_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2423_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2423_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg___boxed(lean_object* v_e_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_2444_, v_a_2445_);
lean_dec_ref(v_a_2445_);
lean_dec_ref(v_e_2444_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr(lean_object* v_e_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v___x_2456_; 
v___x_2456_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_2448_, v_a_2449_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___boxed(lean_object* v_e_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Lean_Meta_Sym_isTrueExpr(v_e_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_);
lean_dec(v_a_2463_);
lean_dec_ref(v_a_2462_);
lean_dec(v_a_2461_);
lean_dec_ref(v_a_2460_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
lean_dec_ref(v_e_2457_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object* v_a_2466_){
_start:
{
lean_object* v___x_2468_; lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2477_; 
v___x_2468_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2466_);
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2471_ = v___x_2468_;
v_isShared_2472_ = v_isSharedCheck_2477_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2468_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2477_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v_falseExpr_2473_; lean_object* v___x_2475_; 
v_falseExpr_2473_ = lean_ctor_get(v_a_2469_, 1);
lean_inc_ref(v_falseExpr_2473_);
lean_dec(v_a_2469_);
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 0, v_falseExpr_2473_);
v___x_2475_ = v___x_2471_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_falseExpr_2473_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg___boxed(lean_object* v_a_2478_, lean_object* v_a_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2478_);
lean_dec_ref(v_a_2478_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr(lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_){
_start:
{
lean_object* v___x_2488_; 
v___x_2488_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2481_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___boxed(lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_Lean_Meta_Sym_getFalseExpr(v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_);
lean_dec(v_a_2494_);
lean_dec_ref(v_a_2493_);
lean_dec(v_a_2492_);
lean_dec_ref(v_a_2491_);
lean_dec(v_a_2490_);
lean_dec_ref(v_a_2489_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object* v_e_2497_, lean_object* v_a_2498_){
_start:
{
lean_object* v___x_2500_; 
v___x_2500_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2498_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2512_; 
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2503_ = v___x_2500_;
v_isShared_2504_ = v_isSharedCheck_2512_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2500_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2512_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
size_t v___x_2505_; size_t v___x_2506_; uint8_t v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2510_; 
v___x_2505_ = lean_ptr_addr(v_e_2497_);
v___x_2506_ = lean_ptr_addr(v_a_2501_);
lean_dec(v_a_2501_);
v___x_2507_ = lean_usize_dec_eq(v___x_2505_, v___x_2506_);
v___x_2508_ = lean_box(v___x_2507_);
if (v_isShared_2504_ == 0)
{
lean_ctor_set(v___x_2503_, 0, v___x_2508_);
v___x_2510_ = v___x_2503_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2508_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
v_a_2513_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2500_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2500_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg___boxed(lean_object* v_e_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_2521_, v_a_2522_);
lean_dec_ref(v_a_2522_);
lean_dec_ref(v_e_2521_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr(lean_object* v_e_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_){
_start:
{
lean_object* v___x_2533_; 
v___x_2533_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_2525_, v_a_2526_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___boxed(lean_object* v_e_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Lean_Meta_Sym_isFalseExpr(v_e_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec(v_a_2536_);
lean_dec_ref(v_a_2535_);
lean_dec_ref(v_e_2534_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object* v_a_2543_){
_start:
{
lean_object* v___x_2545_; lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2554_; 
v___x_2545_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2543_);
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2548_ = v___x_2545_;
v_isShared_2549_ = v_isSharedCheck_2554_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2545_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2554_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v_btrueExpr_2550_; lean_object* v___x_2552_; 
v_btrueExpr_2550_ = lean_ctor_get(v_a_2546_, 3);
lean_inc_ref(v_btrueExpr_2550_);
lean_dec(v_a_2546_);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v_btrueExpr_2550_);
v___x_2552_ = v___x_2548_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_btrueExpr_2550_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg___boxed(lean_object* v_a_2555_, lean_object* v_a_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2555_);
lean_dec_ref(v_a_2555_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr(lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2558_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___boxed(lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_Meta_Sym_getBoolTrueExpr(v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_a_2569_);
lean_dec_ref(v_a_2568_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg(lean_object* v_e_2574_, lean_object* v_a_2575_){
_start:
{
lean_object* v___x_2577_; 
v___x_2577_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2575_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2589_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2589_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2589_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
size_t v___x_2582_; size_t v___x_2583_; uint8_t v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2587_; 
v___x_2582_ = lean_ptr_addr(v_e_2574_);
v___x_2583_ = lean_ptr_addr(v_a_2578_);
lean_dec(v_a_2578_);
v___x_2584_ = lean_usize_dec_eq(v___x_2582_, v___x_2583_);
v___x_2585_ = lean_box(v___x_2584_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2585_);
v___x_2587_ = v___x_2580_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2585_);
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
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
v_a_2590_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2577_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2577_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2590_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg___boxed(lean_object* v_e_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_2598_, v_a_2599_);
lean_dec_ref(v_a_2599_);
lean_dec_ref(v_e_2598_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr(lean_object* v_e_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_){
_start:
{
lean_object* v___x_2610_; 
v___x_2610_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_2602_, v_a_2603_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___boxed(lean_object* v_e_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l_Lean_Meta_Sym_isBoolTrueExpr(v_e_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_);
lean_dec(v_a_2617_);
lean_dec_ref(v_a_2616_);
lean_dec(v_a_2615_);
lean_dec_ref(v_a_2614_);
lean_dec(v_a_2613_);
lean_dec_ref(v_a_2612_);
lean_dec_ref(v_e_2611_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object* v_a_2620_){
_start:
{
lean_object* v___x_2622_; lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2631_; 
v___x_2622_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2620_);
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2625_ = v___x_2622_;
v_isShared_2626_ = v_isSharedCheck_2631_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2622_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2631_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v_bfalseExpr_2627_; lean_object* v___x_2629_; 
v_bfalseExpr_2627_ = lean_ctor_get(v_a_2623_, 4);
lean_inc_ref(v_bfalseExpr_2627_);
lean_dec(v_a_2623_);
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 0, v_bfalseExpr_2627_);
v___x_2629_ = v___x_2625_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_bfalseExpr_2627_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg___boxed(lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2632_);
lean_dec_ref(v_a_2632_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr(lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2635_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___boxed(lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l_Lean_Meta_Sym_getBoolFalseExpr(v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_);
lean_dec(v_a_2648_);
lean_dec_ref(v_a_2647_);
lean_dec(v_a_2646_);
lean_dec_ref(v_a_2645_);
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2643_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg(lean_object* v_e_2651_, lean_object* v_a_2652_){
_start:
{
lean_object* v___x_2654_; 
v___x_2654_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2652_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2666_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2657_ = v___x_2654_;
v_isShared_2658_ = v_isSharedCheck_2666_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2654_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2666_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
size_t v___x_2659_; size_t v___x_2660_; uint8_t v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2664_; 
v___x_2659_ = lean_ptr_addr(v_e_2651_);
v___x_2660_ = lean_ptr_addr(v_a_2655_);
lean_dec(v_a_2655_);
v___x_2661_ = lean_usize_dec_eq(v___x_2659_, v___x_2660_);
v___x_2662_ = lean_box(v___x_2661_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 0, v___x_2662_);
v___x_2664_ = v___x_2657_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2662_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
v_a_2667_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2654_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2654_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg___boxed(lean_object* v_e_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_2675_, v_a_2676_);
lean_dec_ref(v_a_2676_);
lean_dec_ref(v_e_2675_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr(lean_object* v_e_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_){
_start:
{
lean_object* v___x_2687_; 
v___x_2687_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_2679_, v_a_2680_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___boxed(lean_object* v_e_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l_Lean_Meta_Sym_isBoolFalseExpr(v_e_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
lean_dec(v_a_2694_);
lean_dec_ref(v_a_2693_);
lean_dec(v_a_2692_);
lean_dec_ref(v_a_2691_);
lean_dec(v_a_2690_);
lean_dec_ref(v_a_2689_);
lean_dec_ref(v_e_2688_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg(lean_object* v_a_2697_){
_start:
{
lean_object* v___x_2699_; lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2708_; 
v___x_2699_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2697_);
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2702_ = v___x_2699_;
v_isShared_2703_ = v_isSharedCheck_2708_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2699_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2708_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v_natZExpr_2704_; lean_object* v___x_2706_; 
v_natZExpr_2704_ = lean_ctor_get(v_a_2700_, 2);
lean_inc_ref(v_natZExpr_2704_);
lean_dec(v_a_2700_);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 0, v_natZExpr_2704_);
v___x_2706_ = v___x_2702_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_natZExpr_2704_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg___boxed(lean_object* v_a_2709_, lean_object* v_a_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_2709_);
lean_dec_ref(v_a_2709_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr(lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_2712_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___boxed(lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l_Lean_Meta_Sym_getNatZeroExpr(v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_);
lean_dec(v_a_2725_);
lean_dec_ref(v_a_2724_);
lean_dec(v_a_2723_);
lean_dec_ref(v_a_2722_);
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg(lean_object* v_a_2728_){
_start:
{
lean_object* v___x_2730_; lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2739_; 
v___x_2730_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2728_);
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2733_ = v___x_2730_;
v_isShared_2734_ = v_isSharedCheck_2739_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2730_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2739_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v_ordEqExpr_2735_; lean_object* v___x_2737_; 
v_ordEqExpr_2735_ = lean_ctor_get(v_a_2731_, 5);
lean_inc_ref(v_ordEqExpr_2735_);
lean_dec(v_a_2731_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 0, v_ordEqExpr_2735_);
v___x_2737_ = v___x_2733_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_ordEqExpr_2735_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg___boxed(lean_object* v_a_2740_, lean_object* v_a_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_2740_);
lean_dec_ref(v_a_2740_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr(lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_2743_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___boxed(lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Lean_Meta_Sym_getOrderingEqExpr(v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_);
lean_dec(v_a_2756_);
lean_dec_ref(v_a_2755_);
lean_dec(v_a_2754_);
lean_dec_ref(v_a_2753_);
lean_dec(v_a_2752_);
lean_dec_ref(v_a_2751_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg(lean_object* v_a_2759_){
_start:
{
lean_object* v___x_2761_; lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2770_; 
v___x_2761_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2759_);
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2764_ = v___x_2761_;
v_isShared_2765_ = v_isSharedCheck_2770_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2761_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2770_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v_intExpr_2766_; lean_object* v___x_2768_; 
v_intExpr_2766_ = lean_ctor_get(v_a_2762_, 6);
lean_inc_ref(v_intExpr_2766_);
lean_dec(v_a_2762_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v_intExpr_2766_);
v___x_2768_ = v___x_2764_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_intExpr_2766_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg___boxed(lean_object* v_a_2771_, lean_object* v_a_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_2771_);
lean_dec_ref(v_a_2771_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr(lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v___x_2781_; 
v___x_2781_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_2774_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___boxed(lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_Lean_Meta_Sym_getIntExpr(v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_);
lean_dec(v_a_2787_);
lean_dec_ref(v_a_2786_);
lean_dec(v_a_2785_);
lean_dec_ref(v_a_2784_);
lean_dec(v_a_2783_);
lean_dec_ref(v_a_2782_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg(lean_object* v_k_2790_, lean_object* v_ctx_2791_, lean_object* v_a_2792_){
_start:
{
lean_object* v___x_2794_; lean_object* v_share_2795_; lean_object* v_maxFVar_2796_; lean_object* v_proofInstInfo_2797_; lean_object* v_inferType_2798_; lean_object* v_getLevel_2799_; lean_object* v_congrInfo_2800_; lean_object* v_defEqI_2801_; lean_object* v_extensions_2802_; lean_object* v_issues_2803_; lean_object* v_canon_2804_; lean_object* v_instanceOverrides_2805_; uint8_t v_debug_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2866_; 
v___x_2794_ = lean_st_ref_take(v_a_2792_);
v_share_2795_ = lean_ctor_get(v___x_2794_, 0);
v_maxFVar_2796_ = lean_ctor_get(v___x_2794_, 1);
v_proofInstInfo_2797_ = lean_ctor_get(v___x_2794_, 2);
v_inferType_2798_ = lean_ctor_get(v___x_2794_, 3);
v_getLevel_2799_ = lean_ctor_get(v___x_2794_, 4);
v_congrInfo_2800_ = lean_ctor_get(v___x_2794_, 5);
v_defEqI_2801_ = lean_ctor_get(v___x_2794_, 6);
v_extensions_2802_ = lean_ctor_get(v___x_2794_, 7);
v_issues_2803_ = lean_ctor_get(v___x_2794_, 8);
v_canon_2804_ = lean_ctor_get(v___x_2794_, 9);
v_instanceOverrides_2805_ = lean_ctor_get(v___x_2794_, 10);
v_debug_2806_ = lean_ctor_get_uint8(v___x_2794_, sizeof(void*)*11);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2808_ = v___x_2794_;
v_isShared_2809_ = v_isSharedCheck_2866_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_instanceOverrides_2805_);
lean_inc(v_canon_2804_);
lean_inc(v_issues_2803_);
lean_inc(v_extensions_2802_);
lean_inc(v_defEqI_2801_);
lean_inc(v_congrInfo_2800_);
lean_inc(v_getLevel_2799_);
lean_inc(v_inferType_2798_);
lean_inc(v_proofInstInfo_2797_);
lean_inc(v_maxFVar_2796_);
lean_inc(v_share_2795_);
lean_dec(v___x_2794_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2866_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2810_; lean_object* v___x_2812_; 
v___x_2810_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__3, &l_Lean_Meta_Sym_SymM_run___redArg___closed__3_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__3);
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 0, v___x_2810_);
v___x_2812_ = v___x_2808_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2810_);
lean_ctor_set(v_reuseFailAlloc_2865_, 1, v_maxFVar_2796_);
lean_ctor_set(v_reuseFailAlloc_2865_, 2, v_proofInstInfo_2797_);
lean_ctor_set(v_reuseFailAlloc_2865_, 3, v_inferType_2798_);
lean_ctor_set(v_reuseFailAlloc_2865_, 4, v_getLevel_2799_);
lean_ctor_set(v_reuseFailAlloc_2865_, 5, v_congrInfo_2800_);
lean_ctor_set(v_reuseFailAlloc_2865_, 6, v_defEqI_2801_);
lean_ctor_set(v_reuseFailAlloc_2865_, 7, v_extensions_2802_);
lean_ctor_set(v_reuseFailAlloc_2865_, 8, v_issues_2803_);
lean_ctor_set(v_reuseFailAlloc_2865_, 9, v_canon_2804_);
lean_ctor_set(v_reuseFailAlloc_2865_, 10, v_instanceOverrides_2805_);
lean_ctor_set_uint8(v_reuseFailAlloc_2865_, sizeof(void*)*11, v_debug_2806_);
v___x_2812_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = lean_st_ref_put(v_a_2792_, v___x_2812_);
v___x_2814_ = lean_apply_2(v_k_2790_, v_ctx_2791_, v_share_2795_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v_a_2816_; lean_object* v___x_2817_; lean_object* v_maxFVar_2818_; lean_object* v_proofInstInfo_2819_; lean_object* v_inferType_2820_; lean_object* v_getLevel_2821_; lean_object* v_congrInfo_2822_; lean_object* v_defEqI_2823_; lean_object* v_extensions_2824_; lean_object* v_issues_2825_; lean_object* v_canon_2826_; lean_object* v_instanceOverrides_2827_; uint8_t v_debug_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2838_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
v_a_2816_ = lean_ctor_get(v___x_2814_, 1);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___x_2814_, 2);
v___x_2817_ = lean_st_ref_take(v_a_2792_);
v_maxFVar_2818_ = lean_ctor_get(v___x_2817_, 1);
v_proofInstInfo_2819_ = lean_ctor_get(v___x_2817_, 2);
v_inferType_2820_ = lean_ctor_get(v___x_2817_, 3);
v_getLevel_2821_ = lean_ctor_get(v___x_2817_, 4);
v_congrInfo_2822_ = lean_ctor_get(v___x_2817_, 5);
v_defEqI_2823_ = lean_ctor_get(v___x_2817_, 6);
v_extensions_2824_ = lean_ctor_get(v___x_2817_, 7);
v_issues_2825_ = lean_ctor_get(v___x_2817_, 8);
v_canon_2826_ = lean_ctor_get(v___x_2817_, 9);
v_instanceOverrides_2827_ = lean_ctor_get(v___x_2817_, 10);
v_debug_2828_ = lean_ctor_get_uint8(v___x_2817_, sizeof(void*)*11);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2838_ == 0)
{
lean_object* v_unused_2839_; 
v_unused_2839_ = lean_ctor_get(v___x_2817_, 0);
lean_dec(v_unused_2839_);
v___x_2830_ = v___x_2817_;
v_isShared_2831_ = v_isSharedCheck_2838_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_instanceOverrides_2827_);
lean_inc(v_canon_2826_);
lean_inc(v_issues_2825_);
lean_inc(v_extensions_2824_);
lean_inc(v_defEqI_2823_);
lean_inc(v_congrInfo_2822_);
lean_inc(v_getLevel_2821_);
lean_inc(v_inferType_2820_);
lean_inc(v_proofInstInfo_2819_);
lean_inc(v_maxFVar_2818_);
lean_dec(v___x_2817_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2838_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 0, v_a_2816_);
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2816_);
lean_ctor_set(v_reuseFailAlloc_2837_, 1, v_maxFVar_2818_);
lean_ctor_set(v_reuseFailAlloc_2837_, 2, v_proofInstInfo_2819_);
lean_ctor_set(v_reuseFailAlloc_2837_, 3, v_inferType_2820_);
lean_ctor_set(v_reuseFailAlloc_2837_, 4, v_getLevel_2821_);
lean_ctor_set(v_reuseFailAlloc_2837_, 5, v_congrInfo_2822_);
lean_ctor_set(v_reuseFailAlloc_2837_, 6, v_defEqI_2823_);
lean_ctor_set(v_reuseFailAlloc_2837_, 7, v_extensions_2824_);
lean_ctor_set(v_reuseFailAlloc_2837_, 8, v_issues_2825_);
lean_ctor_set(v_reuseFailAlloc_2837_, 9, v_canon_2826_);
lean_ctor_set(v_reuseFailAlloc_2837_, 10, v_instanceOverrides_2827_);
lean_ctor_set_uint8(v_reuseFailAlloc_2837_, sizeof(void*)*11, v_debug_2828_);
v___x_2833_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2834_ = lean_st_ref_put(v_a_2792_, v___x_2833_);
v___x_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2835_, 0, v_a_2815_);
v___x_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2835_);
return v___x_2836_;
}
}
}
else
{
lean_object* v_a_2840_; lean_object* v_a_2841_; lean_object* v___x_2842_; lean_object* v_maxFVar_2843_; lean_object* v_proofInstInfo_2844_; lean_object* v_inferType_2845_; lean_object* v_getLevel_2846_; lean_object* v_congrInfo_2847_; lean_object* v_defEqI_2848_; lean_object* v_extensions_2849_; lean_object* v_issues_2850_; lean_object* v_canon_2851_; lean_object* v_instanceOverrides_2852_; uint8_t v_debug_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2863_; 
v_a_2840_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2840_);
v_a_2841_ = lean_ctor_get(v___x_2814_, 1);
lean_inc(v_a_2841_);
lean_dec_ref_known(v___x_2814_, 2);
v___x_2842_ = lean_st_ref_take(v_a_2792_);
v_maxFVar_2843_ = lean_ctor_get(v___x_2842_, 1);
v_proofInstInfo_2844_ = lean_ctor_get(v___x_2842_, 2);
v_inferType_2845_ = lean_ctor_get(v___x_2842_, 3);
v_getLevel_2846_ = lean_ctor_get(v___x_2842_, 4);
v_congrInfo_2847_ = lean_ctor_get(v___x_2842_, 5);
v_defEqI_2848_ = lean_ctor_get(v___x_2842_, 6);
v_extensions_2849_ = lean_ctor_get(v___x_2842_, 7);
v_issues_2850_ = lean_ctor_get(v___x_2842_, 8);
v_canon_2851_ = lean_ctor_get(v___x_2842_, 9);
v_instanceOverrides_2852_ = lean_ctor_get(v___x_2842_, 10);
v_debug_2853_ = lean_ctor_get_uint8(v___x_2842_, sizeof(void*)*11);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2863_ == 0)
{
lean_object* v_unused_2864_; 
v_unused_2864_ = lean_ctor_get(v___x_2842_, 0);
lean_dec(v_unused_2864_);
v___x_2855_ = v___x_2842_;
v_isShared_2856_ = v_isSharedCheck_2863_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_instanceOverrides_2852_);
lean_inc(v_canon_2851_);
lean_inc(v_issues_2850_);
lean_inc(v_extensions_2849_);
lean_inc(v_defEqI_2848_);
lean_inc(v_congrInfo_2847_);
lean_inc(v_getLevel_2846_);
lean_inc(v_inferType_2845_);
lean_inc(v_proofInstInfo_2844_);
lean_inc(v_maxFVar_2843_);
lean_dec(v___x_2842_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2863_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v_a_2841_);
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2841_);
lean_ctor_set(v_reuseFailAlloc_2862_, 1, v_maxFVar_2843_);
lean_ctor_set(v_reuseFailAlloc_2862_, 2, v_proofInstInfo_2844_);
lean_ctor_set(v_reuseFailAlloc_2862_, 3, v_inferType_2845_);
lean_ctor_set(v_reuseFailAlloc_2862_, 4, v_getLevel_2846_);
lean_ctor_set(v_reuseFailAlloc_2862_, 5, v_congrInfo_2847_);
lean_ctor_set(v_reuseFailAlloc_2862_, 6, v_defEqI_2848_);
lean_ctor_set(v_reuseFailAlloc_2862_, 7, v_extensions_2849_);
lean_ctor_set(v_reuseFailAlloc_2862_, 8, v_issues_2850_);
lean_ctor_set(v_reuseFailAlloc_2862_, 9, v_canon_2851_);
lean_ctor_set(v_reuseFailAlloc_2862_, 10, v_instanceOverrides_2852_);
lean_ctor_set_uint8(v_reuseFailAlloc_2862_, sizeof(void*)*11, v_debug_2853_);
v___x_2858_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2859_ = lean_st_ref_put(v_a_2792_, v___x_2858_);
v___x_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2860_, 0, v_a_2840_);
v___x_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2860_);
return v___x_2861_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg___boxed(lean_object* v_k_2867_, lean_object* v_ctx_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v_k_2867_, v_ctx_2868_, v_a_2869_);
lean_dec(v_a_2869_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM(lean_object* v_00_u03b1_2872_, lean_object* v_k_2873_, lean_object* v_ctx_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v___x_2882_; 
v___x_2882_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v_k_2873_, v_ctx_2874_, v_a_2876_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___boxed(lean_object* v_00_u03b1_2883_, lean_object* v_k_2884_, lean_object* v_ctx_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l_Lean_Meta_Sym_runShareCommonM(v_00_u03b1_2883_, v_k_2884_, v_ctx_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
lean_dec(v_a_2891_);
lean_dec_ref(v_a_2890_);
lean_dec(v_a_2889_);
lean_dec_ref(v_a_2888_);
lean_dec(v_a_2887_);
lean_dec_ref(v_a_2886_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___lam__0(lean_object* v_ctx_2894_){
_start:
{
lean_object* v_config_2895_; lean_object* v_sharedExprs_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2913_; 
v_config_2895_ = lean_ctor_get(v_ctx_2894_, 1);
v_sharedExprs_2896_ = lean_ctor_get(v_ctx_2894_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v_ctx_2894_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2898_ = v_ctx_2894_;
v_isShared_2899_ = v_isSharedCheck_2913_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_config_2895_);
lean_inc(v_sharedExprs_2896_);
lean_dec(v_ctx_2894_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2913_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
uint8_t v_verbose_2900_; uint8_t v_enforceUnfoldReducible_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2912_; 
v_verbose_2900_ = lean_ctor_get_uint8(v_config_2895_, 0);
v_enforceUnfoldReducible_2901_ = lean_ctor_get_uint8(v_config_2895_, 1);
v_isSharedCheck_2912_ = !lean_is_exclusive(v_config_2895_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2903_ = v_config_2895_;
v_isShared_2904_ = v_isSharedCheck_2912_;
goto v_resetjp_2902_;
}
else
{
lean_dec(v_config_2895_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2912_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
uint8_t v___x_2905_; lean_object* v___x_2907_; 
v___x_2905_ = 0;
if (v_isShared_2904_ == 0)
{
v___x_2907_ = v___x_2903_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_2911_, 0, v_verbose_2900_);
lean_ctor_set_uint8(v_reuseFailAlloc_2911_, 1, v_enforceUnfoldReducible_2901_);
v___x_2907_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
lean_object* v___x_2909_; 
lean_ctor_set_uint8(v___x_2907_, 2, v___x_2905_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 1, v___x_2907_);
v___x_2909_ = v___x_2898_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_sharedExprs_2896_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v___x_2907_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg(lean_object* v_inst_2915_, lean_object* v_x_2916_){
_start:
{
lean_object* v___f_2917_; lean_object* v___x_2918_; 
v___f_2917_ = ((lean_object*)(l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___closed__0));
v___x_2918_ = lean_apply_3(v_inst_2915_, lean_box(0), v___f_2917_, v_x_2916_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck(lean_object* v_m_2919_, lean_object* v_00_u03b1_2920_, lean_object* v_inst_2921_, lean_object* v_x_2922_){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg(v_inst_2921_, v_x_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___lam__0(lean_object* v_ctx_2924_){
_start:
{
lean_object* v_config_2925_; lean_object* v_sharedExprs_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2942_; 
v_config_2925_ = lean_ctor_get(v_ctx_2924_, 1);
v_sharedExprs_2926_ = lean_ctor_get(v_ctx_2924_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v_ctx_2924_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2928_ = v_ctx_2924_;
v_isShared_2929_ = v_isSharedCheck_2942_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_config_2925_);
lean_inc(v_sharedExprs_2926_);
lean_dec(v_ctx_2924_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2942_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
uint8_t v_verbose_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2941_; 
v_verbose_2930_ = lean_ctor_get_uint8(v_config_2925_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v_config_2925_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2932_ = v_config_2925_;
v_isShared_2933_ = v_isSharedCheck_2941_;
goto v_resetjp_2931_;
}
else
{
lean_dec(v_config_2925_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2941_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
uint8_t v___x_2934_; lean_object* v___x_2936_; 
v___x_2934_ = 0;
if (v_isShared_2933_ == 0)
{
v___x_2936_ = v___x_2932_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_2940_, 0, v_verbose_2930_);
v___x_2936_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
lean_object* v___x_2938_; 
lean_ctor_set_uint8(v___x_2936_, 1, v___x_2934_);
lean_ctor_set_uint8(v___x_2936_, 2, v___x_2934_);
if (v_isShared_2929_ == 0)
{
lean_ctor_set(v___x_2928_, 1, v___x_2936_);
v___x_2938_ = v___x_2928_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_sharedExprs_2926_);
lean_ctor_set(v_reuseFailAlloc_2939_, 1, v___x_2936_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg(lean_object* v_inst_2944_, lean_object* v_x_2945_){
_start:
{
lean_object* v___f_2946_; lean_object* v___x_2947_; 
v___f_2946_ = ((lean_object*)(l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___closed__0));
v___x_2947_ = lean_apply_3(v_inst_2944_, lean_box(0), v___f_2946_, v_x_2945_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks(lean_object* v_m_2948_, lean_object* v_00_u03b1_2949_, lean_object* v_inst_2950_, lean_object* v_x_2951_){
_start:
{
lean_object* v___x_2952_; 
v___x_2952_ = l_Lean_Meta_Sym_withoutShareCommonChecks___redArg(v_inst_2950_, v_x_2951_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(lean_object* v_a_2953_, lean_object* v_a_2954_){
_start:
{
lean_object* v___x_2956_; lean_object* v_config_2957_; lean_object* v_env_2958_; uint8_t v_enforceUnfoldReducible_2959_; uint8_t v_enforceFoldProjs_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2956_ = lean_st_ref_get(v_a_2954_);
v_config_2957_ = lean_ctor_get(v_a_2953_, 1);
v_env_2958_ = lean_ctor_get(v___x_2956_, 0);
lean_inc_ref(v_env_2958_);
lean_dec(v___x_2956_);
v_enforceUnfoldReducible_2959_ = lean_ctor_get_uint8(v_config_2957_, 1);
v_enforceFoldProjs_2960_ = lean_ctor_get_uint8(v_config_2957_, 2);
v___x_2961_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2961_, 0, v_env_2958_);
lean_ctor_set_uint8(v___x_2961_, sizeof(void*)*1, v_enforceUnfoldReducible_2959_);
lean_ctor_set_uint8(v___x_2961_, sizeof(void*)*1 + 1, v_enforceFoldProjs_2960_);
v___x_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg___boxed(lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_2963_, v_a_2964_);
lean_dec(v_a_2964_);
lean_dec_ref(v_a_2963_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx(lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_){
_start:
{
lean_object* v___x_2974_; 
v___x_2974_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_2967_, v_a_2972_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___boxed(lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx(v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
lean_dec(v_a_2980_);
lean_dec_ref(v_a_2979_);
lean_dec(v_a_2978_);
lean_dec_ref(v_a_2977_);
lean_dec(v_a_2976_);
lean_dec_ref(v_a_2975_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(lean_object* v_e_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_){
_start:
{
lean_object* v_config_2990_; uint8_t v_enforceUnfoldReducible_2991_; uint8_t v_enforceFoldProjs_2992_; lean_object* v_e_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v_e_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; 
v_config_2990_ = lean_ctor_get(v_a_2984_, 1);
v_enforceUnfoldReducible_2991_ = lean_ctor_get_uint8(v_config_2990_, 1);
v_enforceFoldProjs_2992_ = lean_ctor_get_uint8(v_config_2990_, 2);
if (v_enforceUnfoldReducible_2991_ == 0)
{
v_e_3002_ = v_e_2983_;
v___y_3003_ = v_a_2985_;
v___y_3004_ = v_a_2986_;
v___y_3005_ = v_a_2987_;
v___y_3006_ = v_a_2988_;
goto v___jp_3001_;
}
else
{
lean_object* v___x_3009_; 
v___x_3009_ = l_Lean_Meta_Sym_unfoldReducible(v_e_2983_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref_known(v___x_3009_, 1);
v_e_3002_ = v_a_3010_;
v___y_3003_ = v_a_2985_;
v___y_3004_ = v_a_2986_;
v___y_3005_ = v_a_2987_;
v___y_3006_ = v_a_2988_;
goto v___jp_3001_;
}
else
{
return v___x_3009_;
}
}
v___jp_2993_:
{
if (v_enforceUnfoldReducible_2991_ == 0)
{
lean_object* v___x_2999_; 
v___x_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2999_, 0, v_e_2994_);
return v___x_2999_;
}
else
{
lean_object* v___x_3000_; 
v___x_3000_ = l_Lean_Meta_Sym_unfoldReducible(v_e_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_);
return v___x_3000_;
}
}
v___jp_3001_:
{
if (v_enforceFoldProjs_2992_ == 0)
{
v_e_2994_ = v_e_3002_;
v___y_2995_ = v___y_3003_;
v___y_2996_ = v___y_3004_;
v___y_2997_ = v___y_3005_;
v___y_2998_ = v___y_3006_;
goto v___jp_2993_;
}
else
{
lean_object* v___x_3007_; 
v___x_3007_ = l_Lean_Meta_Sym_foldProjs(v_e_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc(v_a_3008_);
lean_dec_ref_known(v___x_3007_, 1);
v_e_2994_ = v_a_3008_;
v___y_2995_ = v___y_3003_;
v___y_2996_ = v___y_3004_;
v___y_2997_ = v___y_3005_;
v___y_2998_ = v___y_3006_;
goto v___jp_2993_;
}
else
{
return v___x_3007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg___boxed(lean_object* v_e_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_);
lean_dec(v_a_3016_);
lean_dec_ref(v_a_3015_);
lean_dec(v_a_3014_);
lean_dec_ref(v_a_3013_);
lean_dec_ref(v_a_3012_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation(lean_object* v_e_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_){
_start:
{
lean_object* v___x_3027_; 
v___x_3027_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3019_, v_a_3020_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___boxed(lean_object* v_e_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation(v_e_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_);
lean_dec(v_a_3034_);
lean_dec_ref(v_a_3033_);
lean_dec(v_a_3032_);
lean_dec_ref(v_a_3031_);
lean_dec(v_a_3030_);
lean_dec_ref(v_a_3029_);
return v_res_3036_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3037_; 
v___x_3037_ = l_instMonadEIO(lean_box(0));
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(lean_object* v_msg_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v_toApplicative_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3115_; 
v___x_3050_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0);
v___x_3051_ = l_StateRefT_x27_instMonad___redArg(v___x_3050_);
v_toApplicative_3052_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3115_ == 0)
{
lean_object* v_unused_3116_; 
v_unused_3116_ = lean_ctor_get(v___x_3051_, 1);
lean_dec(v_unused_3116_);
v___x_3054_ = v___x_3051_;
v_isShared_3055_ = v_isSharedCheck_3115_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_toApplicative_3052_);
lean_dec(v___x_3051_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3115_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v_toFunctor_3056_; lean_object* v_toSeq_3057_; lean_object* v_toSeqLeft_3058_; lean_object* v_toSeqRight_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3113_; 
v_toFunctor_3056_ = lean_ctor_get(v_toApplicative_3052_, 0);
v_toSeq_3057_ = lean_ctor_get(v_toApplicative_3052_, 2);
v_toSeqLeft_3058_ = lean_ctor_get(v_toApplicative_3052_, 3);
v_toSeqRight_3059_ = lean_ctor_get(v_toApplicative_3052_, 4);
v_isSharedCheck_3113_ = !lean_is_exclusive(v_toApplicative_3052_);
if (v_isSharedCheck_3113_ == 0)
{
lean_object* v_unused_3114_; 
v_unused_3114_ = lean_ctor_get(v_toApplicative_3052_, 1);
lean_dec(v_unused_3114_);
v___x_3061_ = v_toApplicative_3052_;
v_isShared_3062_ = v_isSharedCheck_3113_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_toSeqRight_3059_);
lean_inc(v_toSeqLeft_3058_);
lean_inc(v_toSeq_3057_);
lean_inc(v_toFunctor_3056_);
lean_dec(v_toApplicative_3052_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3113_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___f_3063_; lean_object* v___f_3064_; lean_object* v___f_3065_; lean_object* v___f_3066_; lean_object* v___x_3067_; lean_object* v___f_3068_; lean_object* v___f_3069_; lean_object* v___f_3070_; lean_object* v___x_3072_; 
v___f_3063_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1));
v___f_3064_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2));
lean_inc_ref(v_toFunctor_3056_);
v___f_3065_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3065_, 0, v_toFunctor_3056_);
v___f_3066_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3066_, 0, v_toFunctor_3056_);
v___x_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___f_3065_);
lean_ctor_set(v___x_3067_, 1, v___f_3066_);
v___f_3068_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3068_, 0, v_toSeqRight_3059_);
v___f_3069_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3069_, 0, v_toSeqLeft_3058_);
v___f_3070_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3070_, 0, v_toSeq_3057_);
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 4, v___f_3068_);
lean_ctor_set(v___x_3061_, 3, v___f_3069_);
lean_ctor_set(v___x_3061_, 2, v___f_3070_);
lean_ctor_set(v___x_3061_, 1, v___f_3063_);
lean_ctor_set(v___x_3061_, 0, v___x_3067_);
v___x_3072_ = v___x_3061_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v___x_3067_);
lean_ctor_set(v_reuseFailAlloc_3112_, 1, v___f_3063_);
lean_ctor_set(v_reuseFailAlloc_3112_, 2, v___f_3070_);
lean_ctor_set(v_reuseFailAlloc_3112_, 3, v___f_3069_);
lean_ctor_set(v_reuseFailAlloc_3112_, 4, v___f_3068_);
v___x_3072_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
lean_object* v___x_3074_; 
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 1, v___f_3064_);
lean_ctor_set(v___x_3054_, 0, v___x_3072_);
v___x_3074_ = v___x_3054_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3072_);
lean_ctor_set(v_reuseFailAlloc_3111_, 1, v___f_3064_);
v___x_3074_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
lean_object* v___x_3075_; lean_object* v_toApplicative_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3109_; 
v___x_3075_ = l_StateRefT_x27_instMonad___redArg(v___x_3074_);
v_toApplicative_3076_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3109_ == 0)
{
lean_object* v_unused_3110_; 
v_unused_3110_ = lean_ctor_get(v___x_3075_, 1);
lean_dec(v_unused_3110_);
v___x_3078_ = v___x_3075_;
v_isShared_3079_ = v_isSharedCheck_3109_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_toApplicative_3076_);
lean_dec(v___x_3075_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3109_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v_toFunctor_3080_; lean_object* v_toSeq_3081_; lean_object* v_toSeqLeft_3082_; lean_object* v_toSeqRight_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3107_; 
v_toFunctor_3080_ = lean_ctor_get(v_toApplicative_3076_, 0);
v_toSeq_3081_ = lean_ctor_get(v_toApplicative_3076_, 2);
v_toSeqLeft_3082_ = lean_ctor_get(v_toApplicative_3076_, 3);
v_toSeqRight_3083_ = lean_ctor_get(v_toApplicative_3076_, 4);
v_isSharedCheck_3107_ = !lean_is_exclusive(v_toApplicative_3076_);
if (v_isSharedCheck_3107_ == 0)
{
lean_object* v_unused_3108_; 
v_unused_3108_ = lean_ctor_get(v_toApplicative_3076_, 1);
lean_dec(v_unused_3108_);
v___x_3085_ = v_toApplicative_3076_;
v_isShared_3086_ = v_isSharedCheck_3107_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_toSeqRight_3083_);
lean_inc(v_toSeqLeft_3082_);
lean_inc(v_toSeq_3081_);
lean_inc(v_toFunctor_3080_);
lean_dec(v_toApplicative_3076_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3107_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___f_3087_; lean_object* v___f_3088_; lean_object* v___f_3089_; lean_object* v___f_3090_; lean_object* v___x_3091_; lean_object* v___f_3092_; lean_object* v___f_3093_; lean_object* v___f_3094_; lean_object* v___x_3096_; 
v___f_3087_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3));
v___f_3088_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4));
lean_inc_ref(v_toFunctor_3080_);
v___f_3089_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3089_, 0, v_toFunctor_3080_);
v___f_3090_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3090_, 0, v_toFunctor_3080_);
v___x_3091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3091_, 0, v___f_3089_);
lean_ctor_set(v___x_3091_, 1, v___f_3090_);
v___f_3092_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3092_, 0, v_toSeqRight_3083_);
v___f_3093_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3093_, 0, v_toSeqLeft_3082_);
v___f_3094_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3094_, 0, v_toSeq_3081_);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 4, v___f_3092_);
lean_ctor_set(v___x_3085_, 3, v___f_3093_);
lean_ctor_set(v___x_3085_, 2, v___f_3094_);
lean_ctor_set(v___x_3085_, 1, v___f_3087_);
lean_ctor_set(v___x_3085_, 0, v___x_3091_);
v___x_3096_ = v___x_3085_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v___x_3091_);
lean_ctor_set(v_reuseFailAlloc_3106_, 1, v___f_3087_);
lean_ctor_set(v_reuseFailAlloc_3106_, 2, v___f_3094_);
lean_ctor_set(v_reuseFailAlloc_3106_, 3, v___f_3093_);
lean_ctor_set(v_reuseFailAlloc_3106_, 4, v___f_3092_);
v___x_3096_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
lean_object* v___x_3098_; 
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 1, v___f_3088_);
lean_ctor_set(v___x_3078_, 0, v___x_3096_);
v___x_3098_ = v___x_3078_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3096_);
lean_ctor_set(v_reuseFailAlloc_3105_, 1, v___f_3088_);
v___x_3098_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___f_3102_; lean_object* v___x_909__overap_3103_; lean_object* v___x_3104_; 
v___x_3099_ = l_StateRefT_x27_instMonad___redArg(v___x_3098_);
v___x_3100_ = l_Lean_instInhabitedExpr;
v___x_3101_ = l_instInhabitedOfMonad___redArg(v___x_3099_, v___x_3100_);
v___f_3102_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3102_, 0, v___x_3101_);
v___x_909__overap_3103_ = lean_panic_fn_borrowed(v___f_3102_, v_msg_3042_);
lean_dec_ref(v___f_3102_);
lean_inc(v___y_3048_);
lean_inc_ref(v___y_3047_);
lean_inc(v___y_3046_);
lean_inc_ref(v___y_3045_);
lean_inc(v___y_3044_);
lean_inc_ref(v___y_3043_);
v___x_3104_ = lean_apply_7(v___x_909__overap_3103_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, lean_box(0));
return v___x_3104_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___boxed(lean_object* v_msg_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(v_msg_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_3126_, lean_object* v_vals_3127_, lean_object* v_i_3128_, lean_object* v_k_3129_){
_start:
{
lean_object* v___x_3130_; uint8_t v___x_3131_; 
v___x_3130_ = lean_array_get_size(v_keys_3126_);
v___x_3131_ = lean_nat_dec_lt(v_i_3128_, v___x_3130_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3132_; 
lean_dec(v_i_3128_);
v___x_3132_ = lean_box(0);
return v___x_3132_;
}
else
{
lean_object* v_k_x27_3133_; uint8_t v___x_3134_; 
v_k_x27_3133_ = lean_array_fget_borrowed(v_keys_3126_, v_i_3128_);
v___x_3134_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_3129_, v_k_x27_3133_);
if (v___x_3134_ == 0)
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3135_ = lean_unsigned_to_nat(1u);
v___x_3136_ = lean_nat_add(v_i_3128_, v___x_3135_);
lean_dec(v_i_3128_);
v_i_3128_ = v___x_3136_;
goto _start;
}
else
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3138_ = lean_array_fget_borrowed(v_vals_3127_, v_i_3128_);
lean_dec(v_i_3128_);
lean_inc(v___x_3138_);
lean_inc(v_k_x27_3133_);
v___x_3139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3139_, 0, v_k_x27_3133_);
lean_ctor_set(v___x_3139_, 1, v___x_3138_);
v___x_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3139_);
return v___x_3140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_3141_, lean_object* v_vals_3142_, lean_object* v_i_3143_, lean_object* v_k_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_keys_3141_, v_vals_3142_, v_i_3143_, v_k_3144_);
lean_dec_ref(v_k_3144_);
lean_dec_ref(v_vals_3142_);
lean_dec_ref(v_keys_3141_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(lean_object* v_x_3146_, size_t v_x_3147_, lean_object* v_x_3148_){
_start:
{
if (lean_obj_tag(v_x_3146_) == 0)
{
lean_object* v_es_3149_; lean_object* v___x_3150_; size_t v___x_3151_; size_t v___x_3152_; lean_object* v_j_3153_; lean_object* v___x_3154_; 
v_es_3149_ = lean_ctor_get(v_x_3146_, 0);
v___x_3150_ = lean_box(2);
v___x_3151_ = ((size_t)31ULL);
v___x_3152_ = lean_usize_land(v_x_3147_, v___x_3151_);
v_j_3153_ = lean_usize_to_nat(v___x_3152_);
v___x_3154_ = lean_array_get_borrowed(v___x_3150_, v_es_3149_, v_j_3153_);
lean_dec(v_j_3153_);
switch(lean_obj_tag(v___x_3154_))
{
case 0:
{
lean_object* v_key_3155_; lean_object* v_val_3156_; uint8_t v___x_3157_; 
v_key_3155_ = lean_ctor_get(v___x_3154_, 0);
v_val_3156_ = lean_ctor_get(v___x_3154_, 1);
v___x_3157_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_3148_, v_key_3155_);
if (v___x_3157_ == 0)
{
lean_object* v___x_3158_; 
v___x_3158_ = lean_box(0);
return v___x_3158_;
}
else
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
lean_inc(v_val_3156_);
lean_inc(v_key_3155_);
v___x_3159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3159_, 0, v_key_3155_);
lean_ctor_set(v___x_3159_, 1, v_val_3156_);
v___x_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
return v___x_3160_;
}
}
case 1:
{
lean_object* v_node_3161_; size_t v___x_3162_; size_t v___x_3163_; 
v_node_3161_ = lean_ctor_get(v___x_3154_, 0);
v___x_3162_ = ((size_t)5ULL);
v___x_3163_ = lean_usize_shift_right(v_x_3147_, v___x_3162_);
v_x_3146_ = v_node_3161_;
v_x_3147_ = v___x_3163_;
goto _start;
}
default: 
{
lean_object* v___x_3165_; 
v___x_3165_ = lean_box(0);
return v___x_3165_;
}
}
}
else
{
lean_object* v_ks_3166_; lean_object* v_vs_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v_ks_3166_ = lean_ctor_get(v_x_3146_, 0);
v_vs_3167_ = lean_ctor_get(v_x_3146_, 1);
v___x_3168_ = lean_unsigned_to_nat(0u);
v___x_3169_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_ks_3166_, v_vs_3167_, v___x_3168_, v_x_3148_);
return v___x_3169_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg___boxed(lean_object* v_x_3170_, lean_object* v_x_3171_, lean_object* v_x_3172_){
_start:
{
size_t v_x_1228__boxed_3173_; lean_object* v_res_3174_; 
v_x_1228__boxed_3173_ = lean_unbox_usize(v_x_3171_);
lean_dec(v_x_3171_);
v_res_3174_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3170_, v_x_1228__boxed_3173_, v_x_3172_);
lean_dec_ref(v_x_3172_);
lean_dec_ref(v_x_3170_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(lean_object* v_x_3175_, lean_object* v_x_3176_){
_start:
{
uint64_t v___x_3177_; size_t v___x_3178_; lean_object* v___x_3179_; 
v___x_3177_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_3176_);
v___x_3178_ = lean_uint64_to_usize(v___x_3177_);
v___x_3179_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3175_, v___x_3178_, v_x_3176_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg___boxed(lean_object* v_x_3180_, lean_object* v_x_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v_x_3180_, v_x_3181_);
lean_dec_ref(v_x_3181_);
lean_dec_ref(v_x_3180_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0(lean_object* v_e_3183_, lean_object* v_cache_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v___x_3187_; 
v___x_3187_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v___y_3186_, v_e_3183_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3188_, 0, v_cache_3184_);
lean_ctor_set(v___x_3188_, 1, v___y_3186_);
v___x_3189_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_3183_, v___y_3185_, v___x_3188_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v_a_3190_; lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3199_; 
v_a_3190_ = lean_ctor_get(v___x_3189_, 1);
v_a_3191_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3193_ = v___x_3189_;
v_isShared_3194_ = v_isSharedCheck_3199_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3190_);
lean_inc(v_a_3191_);
lean_dec(v___x_3189_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3199_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v_set_3195_; lean_object* v___x_3197_; 
v_set_3195_ = lean_ctor_get(v_a_3190_, 1);
lean_inc_ref(v_set_3195_);
lean_dec(v_a_3190_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 1, v_set_3195_);
v___x_3197_ = v___x_3193_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3191_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v_set_3195_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3209_; 
v_a_3200_ = lean_ctor_get(v___x_3189_, 1);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3209_ == 0)
{
lean_object* v_unused_3210_; 
v_unused_3210_ = lean_ctor_get(v___x_3189_, 0);
lean_dec(v_unused_3210_);
v___x_3202_ = v___x_3189_;
v_isShared_3203_ = v_isSharedCheck_3209_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3189_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3209_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v_map_3204_; lean_object* v_set_3205_; lean_object* v___x_3207_; 
v_map_3204_ = lean_ctor_get(v_a_3200_, 0);
lean_inc_ref(v_map_3204_);
v_set_3205_ = lean_ctor_get(v_a_3200_, 1);
lean_inc_ref(v_set_3205_);
lean_dec(v_a_3200_);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 1, v_set_3205_);
lean_ctor_set(v___x_3202_, 0, v_map_3204_);
v___x_3207_ = v___x_3202_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_map_3204_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_set_3205_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
else
{
lean_object* v_val_3211_; lean_object* v_fst_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3219_; 
lean_dec_ref(v_cache_3184_);
lean_dec_ref(v_e_3183_);
v_val_3211_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_val_3211_);
lean_dec_ref_known(v___x_3187_, 1);
v_fst_3212_ = lean_ctor_get(v_val_3211_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v_val_3211_);
if (v_isSharedCheck_3219_ == 0)
{
lean_object* v_unused_3220_; 
v_unused_3220_ = lean_ctor_get(v_val_3211_, 1);
lean_dec(v_unused_3220_);
v___x_3214_ = v_val_3211_;
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_fst_3212_);
lean_dec(v_val_3211_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3217_; 
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 1, v___y_3186_);
v___x_3217_ = v___x_3214_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_fst_3212_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v___y_3186_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0___boxed(lean_object* v_e_3221_, lean_object* v_cache_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0(v_e_3221_, v_cache_3222_, v___y_3223_, v___y_3224_);
lean_dec_ref(v___y_3223_);
return v_res_3225_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1(void){
_start:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3227_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__6));
v___x_3228_ = lean_unsigned_to_nat(16u);
v___x_3229_ = lean_unsigned_to_nat(396u);
v___x_3230_ = ((lean_object*)(l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__0));
v___x_3231_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__4));
v___x_3232_ = l_mkPanicMessageWithDecl(v___x_3231_, v___x_3230_, v___x_3229_, v___x_3228_, v___x_3227_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks(lean_object* v_e_3233_, lean_object* v_cache_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_){
_start:
{
lean_object* v___x_3242_; lean_object* v_env_3243_; lean_object* v___f_3244_; uint8_t v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3258_; 
v___x_3242_ = lean_st_ref_get(v_a_3240_);
v_env_3243_ = lean_ctor_get(v___x_3242_, 0);
lean_inc_ref(v_env_3243_);
lean_dec(v___x_3242_);
v___f_3244_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3244_, 0, v_e_3233_);
lean_closure_set(v___f_3244_, 1, v_cache_3234_);
v___x_3245_ = 0;
v___x_3246_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3246_, 0, v_env_3243_);
lean_ctor_set_uint8(v___x_3246_, sizeof(void*)*1, v___x_3245_);
lean_ctor_set_uint8(v___x_3246_, sizeof(void*)*1 + 1, v___x_3245_);
v___x_3247_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3244_, v___x_3246_, v_a_3236_);
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3250_ = v___x_3247_;
v_isShared_3251_ = v_isSharedCheck_3258_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3247_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3258_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
if (lean_obj_tag(v_a_3248_) == 0)
{
lean_object* v___x_3252_; lean_object* v___x_3253_; 
lean_dec_ref_known(v_a_3248_, 1);
lean_del_object(v___x_3250_);
v___x_3252_ = lean_obj_once(&l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1, &l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1_once, _init_l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1);
v___x_3253_ = l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(v___x_3252_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_);
return v___x_3253_;
}
else
{
lean_object* v_a_3254_; lean_object* v___x_3256_; 
v_a_3254_ = lean_ctor_get(v_a_3248_, 0);
lean_inc(v_a_3254_);
lean_dec_ref_known(v_a_3248_, 1);
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 0, v_a_3254_);
v___x_3256_ = v___x_3250_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3254_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___boxed(lean_object* v_e_3259_, lean_object* v_cache_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_){
_start:
{
lean_object* v_res_3268_; 
v_res_3268_ = l_Lean_Meta_Sym_shareCommonWithoutChecks(v_e_3259_, v_cache_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_);
lean_dec(v_a_3266_);
lean_dec_ref(v_a_3265_);
lean_dec(v_a_3264_);
lean_dec_ref(v_a_3263_);
lean_dec(v_a_3262_);
lean_dec_ref(v_a_3261_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0(lean_object* v_00_u03b2_3269_, lean_object* v_x_3270_, lean_object* v_x_3271_){
_start:
{
lean_object* v___x_3272_; 
v___x_3272_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v_x_3270_, v_x_3271_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___boxed(lean_object* v_00_u03b2_3273_, lean_object* v_x_3274_, lean_object* v_x_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0(v_00_u03b2_3273_, v_x_3274_, v_x_3275_);
lean_dec_ref(v_x_3275_);
lean_dec_ref(v_x_3274_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0(lean_object* v_00_u03b2_3277_, lean_object* v_x_3278_, size_t v_x_3279_, lean_object* v_x_3280_){
_start:
{
lean_object* v___x_3281_; 
v___x_3281_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3278_, v_x_3279_, v_x_3280_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3282_, lean_object* v_x_3283_, lean_object* v_x_3284_, lean_object* v_x_3285_){
_start:
{
size_t v_x_1433__boxed_3286_; lean_object* v_res_3287_; 
v_x_1433__boxed_3286_ = lean_unbox_usize(v_x_3284_);
lean_dec(v_x_3284_);
v_res_3287_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0(v_00_u03b2_3282_, v_x_3283_, v_x_1433__boxed_3286_, v_x_3285_);
lean_dec_ref(v_x_3285_);
lean_dec_ref(v_x_3283_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3288_, lean_object* v_keys_3289_, lean_object* v_vals_3290_, lean_object* v_heq_3291_, lean_object* v_i_3292_, lean_object* v_k_3293_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_keys_3289_, v_vals_3290_, v_i_3292_, v_k_3293_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3295_, lean_object* v_keys_3296_, lean_object* v_vals_3297_, lean_object* v_heq_3298_, lean_object* v_i_3299_, lean_object* v_k_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2(v_00_u03b2_3295_, v_keys_3296_, v_vals_3297_, v_heq_3298_, v_i_3299_, v_k_3300_);
lean_dec_ref(v_k_3300_);
lean_dec_ref(v_vals_3297_);
lean_dec_ref(v_keys_3296_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(lean_object* v_msg_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
lean_object* v_ref_3308_; lean_object* v___x_3309_; lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3318_; 
v_ref_3308_ = lean_ctor_get(v___y_3305_, 4);
v___x_3309_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3312_ = v___x_3309_;
v_isShared_3313_ = v_isSharedCheck_3318_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3309_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3318_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3314_; lean_object* v___x_3316_; 
lean_inc(v_ref_3308_);
v___x_3314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3314_, 0, v_ref_3308_);
lean_ctor_set(v___x_3314_, 1, v_a_3310_);
if (v_isShared_3313_ == 0)
{
lean_ctor_set_tag(v___x_3312_, 1);
lean_ctor_set(v___x_3312_, 0, v___x_3314_);
v___x_3316_ = v___x_3312_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3314_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg___boxed(lean_object* v_msg_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v_res_3325_; 
v_res_3325_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v_msg_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
return v_res_3325_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1(void){
_start:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3327_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__0));
v___x_3328_ = l_Lean_stringToMessageData(v___x_3327_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(lean_object* v_e_3329_, lean_object* v_cache_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_){
_start:
{
lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; uint8_t v___x_3348_; 
v___x_3348_ = l_Lean_Expr_hasLooseBVars(v_e_3329_);
if (v___x_3348_ == 0)
{
v___y_3339_ = v_a_3331_;
v___y_3340_ = v_a_3332_;
v___y_3341_ = v_a_3333_;
v___y_3342_ = v_a_3334_;
v___y_3343_ = v_a_3335_;
v___y_3344_ = v_a_3336_;
goto v___jp_3338_;
}
else
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3360_; 
lean_dec_ref(v_cache_3330_);
v___x_3349_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1);
v___x_3350_ = l_Lean_indentExpr(v_e_3329_);
v___x_3351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3349_);
lean_ctor_set(v___x_3351_, 1, v___x_3350_);
v___x_3352_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v___x_3351_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_);
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3355_ = v___x_3352_;
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3352_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3358_; 
if (v_isShared_3356_ == 0)
{
v___x_3358_ = v___x_3355_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_a_3353_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
v___jp_3338_:
{
lean_object* v___x_3345_; 
v___x_3345_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3329_, v___y_3339_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; lean_object* v___x_3347_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_a_3346_);
lean_dec_ref_known(v___x_3345_, 1);
v___x_3347_ = l_Lean_Meta_Sym_shareCommonWithoutChecks(v_a_3346_, v_cache_3330_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
return v___x_3347_;
}
else
{
lean_dec_ref(v_cache_3330_);
return v___x_3345_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___boxed(lean_object* v_e_3361_, lean_object* v_cache_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3361_, v_cache_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
lean_dec(v_a_3368_);
lean_dec_ref(v_a_3367_);
lean_dec(v_a_3366_);
lean_dec_ref(v_a_3365_);
lean_dec(v_a_3364_);
lean_dec_ref(v_a_3363_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0(lean_object* v_00_u03b1_3371_, lean_object* v_msg_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
lean_object* v___x_3380_; 
v___x_3380_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v_msg_3372_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___boxed(lean_object* v_00_u03b1_3381_, lean_object* v_msg_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0(v_00_u03b1_3381_, v_msg_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___lam__0(lean_object* v_e_3391_, lean_object* v___x_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v___x_3395_; 
v___x_3395_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v___y_3394_, v_e_3391_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3392_);
lean_ctor_set(v___x_3396_, 1, v___y_3394_);
v___x_3397_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_3391_, v___y_3393_, v___x_3396_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_a_3398_; lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3407_; 
v_a_3398_ = lean_ctor_get(v___x_3397_, 1);
v_a_3399_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3401_ = v___x_3397_;
v_isShared_3402_ = v_isSharedCheck_3407_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3398_);
lean_inc(v_a_3399_);
lean_dec(v___x_3397_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3407_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v_set_3403_; lean_object* v___x_3405_; 
v_set_3403_ = lean_ctor_get(v_a_3398_, 1);
lean_inc_ref(v_set_3403_);
lean_dec(v_a_3398_);
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 1, v_set_3403_);
v___x_3405_ = v___x_3401_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3399_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v_set_3403_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
else
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3417_; 
v_a_3408_ = lean_ctor_get(v___x_3397_, 1);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3417_ == 0)
{
lean_object* v_unused_3418_; 
v_unused_3418_ = lean_ctor_get(v___x_3397_, 0);
lean_dec(v_unused_3418_);
v___x_3410_ = v___x_3397_;
v_isShared_3411_ = v_isSharedCheck_3417_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3397_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3417_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v_map_3412_; lean_object* v_set_3413_; lean_object* v___x_3415_; 
v_map_3412_ = lean_ctor_get(v_a_3408_, 0);
lean_inc_ref(v_map_3412_);
v_set_3413_ = lean_ctor_get(v_a_3408_, 1);
lean_inc_ref(v_set_3413_);
lean_dec(v_a_3408_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 1, v_set_3413_);
lean_ctor_set(v___x_3410_, 0, v_map_3412_);
v___x_3415_ = v___x_3410_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_map_3412_);
lean_ctor_set(v_reuseFailAlloc_3416_, 1, v_set_3413_);
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
else
{
lean_object* v_val_3419_; lean_object* v_fst_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3427_; 
lean_dec_ref(v___x_3392_);
lean_dec_ref(v_e_3391_);
v_val_3419_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_val_3419_);
lean_dec_ref_known(v___x_3395_, 1);
v_fst_3420_ = lean_ctor_get(v_val_3419_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v_val_3419_);
if (v_isSharedCheck_3427_ == 0)
{
lean_object* v_unused_3428_; 
v_unused_3428_ = lean_ctor_get(v_val_3419_, 1);
lean_dec(v_unused_3428_);
v___x_3422_ = v_val_3419_;
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_fst_3420_);
lean_dec(v_val_3419_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 1, v___y_3394_);
v___x_3425_ = v___x_3422_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_fst_3420_);
lean_ctor_set(v_reuseFailAlloc_3426_, 1, v___y_3394_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___lam__0___boxed(lean_object* v_e_3429_, lean_object* v___x_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lean_Meta_Sym_shareCommon___lam__0(v_e_3429_, v___x_3430_, v___y_3431_, v___y_3432_);
lean_dec_ref(v___y_3431_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon(lean_object* v_e_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_){
_start:
{
lean_object* v___x_3442_; lean_object* v_a_3443_; lean_object* v___x_3444_; lean_object* v___f_3445_; lean_object* v___x_3446_; lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3457_; 
v___x_3442_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3435_, v_a_3440_);
v_a_3443_ = lean_ctor_get(v___x_3442_, 0);
lean_inc(v_a_3443_);
lean_dec_ref(v___x_3442_);
v___x_3444_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
lean_inc_ref(v_e_3434_);
v___f_3445_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommon___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3445_, 0, v_e_3434_);
lean_closure_set(v___f_3445_, 1, v___x_3444_);
v___x_3446_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3445_, v_a_3443_, v_a_3436_);
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3449_ = v___x_3446_;
v_isShared_3450_ = v_isSharedCheck_3457_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3446_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3457_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
if (lean_obj_tag(v_a_3447_) == 0)
{
lean_object* v_a_3451_; lean_object* v___x_3452_; 
lean_del_object(v___x_3449_);
v_a_3451_ = lean_ctor_get(v_a_3447_, 0);
lean_inc(v_a_3451_);
lean_dec_ref_known(v_a_3447_, 1);
v___x_3452_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3434_, v_a_3451_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_);
return v___x_3452_;
}
else
{
lean_object* v_a_3453_; lean_object* v___x_3455_; 
lean_dec_ref(v_e_3434_);
v_a_3453_ = lean_ctor_get(v_a_3447_, 0);
lean_inc(v_a_3453_);
lean_dec_ref_known(v_a_3447_, 1);
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 0, v_a_3453_);
v___x_3455_ = v___x_3449_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_a_3453_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___boxed(lean_object* v_e_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_){
_start:
{
lean_object* v_res_3466_; 
v_res_3466_ = l_Lean_Meta_Sym_shareCommon(v_e_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_);
lean_dec(v_a_3464_);
lean_dec_ref(v_a_3463_);
lean_dec(v_a_3462_);
lean_dec_ref(v_a_3461_);
lean_dec(v_a_3460_);
lean_dec_ref(v_a_3459_);
return v_res_3466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___lam__0(lean_object* v_e_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v___x_3470_; 
v___x_3470_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_3467_, v___y_3468_, v___y_3469_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___lam__0___boxed(lean_object* v_e_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l_Lean_Meta_Sym_shareCommonInc___lam__0(v_e_3471_, v___y_3472_, v___y_3473_);
lean_dec_ref(v___y_3472_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object* v_e_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_){
_start:
{
lean_object* v___x_3483_; lean_object* v_a_3484_; lean_object* v___f_3485_; lean_object* v___x_3486_; lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3497_; 
v___x_3483_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3476_, v_a_3481_);
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
lean_inc(v_a_3484_);
lean_dec_ref(v___x_3483_);
lean_inc_ref(v_e_3475_);
v___f_3485_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommonInc___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3485_, 0, v_e_3475_);
v___x_3486_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3485_, v_a_3484_, v_a_3477_);
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3489_ = v___x_3486_;
v_isShared_3490_ = v_isSharedCheck_3497_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3486_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3497_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
if (lean_obj_tag(v_a_3487_) == 0)
{
lean_object* v___x_3491_; lean_object* v___x_3492_; 
lean_dec_ref_known(v_a_3487_, 1);
lean_del_object(v___x_3489_);
v___x_3491_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_3492_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3475_, v___x_3491_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_);
return v___x_3492_;
}
else
{
lean_object* v_a_3493_; lean_object* v___x_3495_; 
lean_dec_ref(v_e_3475_);
v_a_3493_ = lean_ctor_get(v_a_3487_, 0);
lean_inc(v_a_3493_);
lean_dec_ref_known(v_a_3487_, 1);
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 0, v_a_3493_);
v___x_3495_ = v___x_3489_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3493_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___boxed(lean_object* v_e_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_){
_start:
{
lean_object* v_res_3506_; 
v_res_3506_ = l_Lean_Meta_Sym_shareCommonInc(v_e_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_);
lean_dec(v_a_3504_);
lean_dec_ref(v_a_3503_);
lean_dec(v_a_3502_);
lean_dec_ref(v_a_3501_);
lean_dec(v_a_3500_);
lean_dec_ref(v_a_3499_);
return v_res_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share(lean_object* v_e_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_){
_start:
{
lean_object* v___x_3515_; 
v___x_3515_ = l_Lean_Meta_Sym_shareCommonInc(v_e_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___boxed(lean_object* v_e_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_){
_start:
{
lean_object* v_res_3524_; 
v_res_3524_ = l_Lean_Meta_Sym_share(v_e_3516_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_);
lean_dec(v_a_3522_);
lean_dec_ref(v_a_3521_);
lean_dec(v_a_3520_);
lean_dec_ref(v_a_3519_);
lean_dec(v_a_3518_);
lean_dec_ref(v_a_3517_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg(lean_object* v_a_3525_){
_start:
{
lean_object* v___x_3527_; uint8_t v_debug_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3527_ = lean_st_ref_get(v_a_3525_);
v_debug_3528_ = lean_ctor_get_uint8(v___x_3527_, sizeof(void*)*11);
lean_dec(v___x_3527_);
v___x_3529_ = lean_box(v_debug_3528_);
v___x_3530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3529_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg___boxed(lean_object* v_a_3531_, lean_object* v_a_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Lean_Meta_Sym_isDebugEnabled___redArg(v_a_3531_);
lean_dec(v_a_3531_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled(lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_){
_start:
{
lean_object* v___x_3541_; uint8_t v_debug_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3541_ = lean_st_ref_get(v_a_3535_);
v_debug_3542_ = lean_ctor_get_uint8(v___x_3541_, sizeof(void*)*11);
lean_dec(v___x_3541_);
v___x_3543_ = lean_box(v_debug_3542_);
v___x_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3543_);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___boxed(lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_){
_start:
{
lean_object* v_res_3552_; 
v_res_3552_ = l_Lean_Meta_Sym_isDebugEnabled(v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_);
lean_dec(v_a_3550_);
lean_dec_ref(v_a_3549_);
lean_dec(v_a_3548_);
lean_dec_ref(v_a_3547_);
lean_dec(v_a_3546_);
lean_dec_ref(v_a_3545_);
return v_res_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object* v_a_3553_){
_start:
{
lean_object* v_config_3555_; lean_object* v___x_3556_; 
v_config_3555_ = lean_ctor_get(v_a_3553_, 1);
lean_inc_ref(v_config_3555_);
v___x_3556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3556_, 0, v_config_3555_);
return v___x_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg___boxed(lean_object* v_a_3557_, lean_object* v_a_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3557_);
lean_dec_ref(v_a_3557_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig(lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_){
_start:
{
lean_object* v___x_3567_; 
v___x_3567_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3560_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___boxed(lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l_Lean_Meta_Sym_getConfig(v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_);
lean_dec(v_a_3573_);
lean_dec_ref(v_a_3572_);
lean_dec(v_a_3571_);
lean_dec_ref(v_a_3570_);
lean_dec(v_a_3569_);
lean_dec_ref(v_a_3568_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(lean_object* v_cls_3576_, lean_object* v_msg_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_){
_start:
{
lean_object* v_ref_3583_; lean_object* v___x_3584_; lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3629_; 
v_ref_3583_ = lean_ctor_get(v___y_3580_, 4);
v___x_3584_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
v_a_3585_ = lean_ctor_get(v___x_3584_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3584_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3587_ = v___x_3584_;
v_isShared_3588_ = v_isSharedCheck_3629_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v___x_3584_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3629_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3589_; lean_object* v_traceState_3590_; lean_object* v_env_3591_; lean_object* v_nextMacroScope_3592_; lean_object* v_ngen_3593_; lean_object* v_auxDeclNGen_3594_; lean_object* v_cache_3595_; lean_object* v_messages_3596_; lean_object* v_infoState_3597_; lean_object* v_snapshotTasks_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3628_; 
v___x_3589_ = lean_st_ref_take(v___y_3581_);
v_traceState_3590_ = lean_ctor_get(v___x_3589_, 4);
v_env_3591_ = lean_ctor_get(v___x_3589_, 0);
v_nextMacroScope_3592_ = lean_ctor_get(v___x_3589_, 1);
v_ngen_3593_ = lean_ctor_get(v___x_3589_, 2);
v_auxDeclNGen_3594_ = lean_ctor_get(v___x_3589_, 3);
v_cache_3595_ = lean_ctor_get(v___x_3589_, 5);
v_messages_3596_ = lean_ctor_get(v___x_3589_, 6);
v_infoState_3597_ = lean_ctor_get(v___x_3589_, 7);
v_snapshotTasks_3598_ = lean_ctor_get(v___x_3589_, 8);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3600_ = v___x_3589_;
v_isShared_3601_ = v_isSharedCheck_3628_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_snapshotTasks_3598_);
lean_inc(v_infoState_3597_);
lean_inc(v_messages_3596_);
lean_inc(v_cache_3595_);
lean_inc(v_traceState_3590_);
lean_inc(v_auxDeclNGen_3594_);
lean_inc(v_ngen_3593_);
lean_inc(v_nextMacroScope_3592_);
lean_inc(v_env_3591_);
lean_dec(v___x_3589_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3628_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
uint64_t v_tid_3602_; lean_object* v_traces_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3627_; 
v_tid_3602_ = lean_ctor_get_uint64(v_traceState_3590_, sizeof(void*)*1);
v_traces_3603_ = lean_ctor_get(v_traceState_3590_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v_traceState_3590_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3605_ = v_traceState_3590_;
v_isShared_3606_ = v_isSharedCheck_3627_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_traces_3603_);
lean_dec(v_traceState_3590_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3627_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3607_; double v___x_3608_; uint8_t v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3617_; 
v___x_3607_ = lean_box(0);
v___x_3608_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_3609_ = 0;
v___x_3610_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_3611_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3611_, 0, v_cls_3576_);
lean_ctor_set(v___x_3611_, 1, v___x_3607_);
lean_ctor_set(v___x_3611_, 2, v___x_3610_);
lean_ctor_set_float(v___x_3611_, sizeof(void*)*3, v___x_3608_);
lean_ctor_set_float(v___x_3611_, sizeof(void*)*3 + 8, v___x_3608_);
lean_ctor_set_uint8(v___x_3611_, sizeof(void*)*3 + 16, v___x_3609_);
v___x_3612_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
v___x_3613_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3611_);
lean_ctor_set(v___x_3613_, 1, v_a_3585_);
lean_ctor_set(v___x_3613_, 2, v___x_3612_);
lean_inc(v_ref_3583_);
v___x_3614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3614_, 0, v_ref_3583_);
lean_ctor_set(v___x_3614_, 1, v___x_3613_);
v___x_3615_ = l_Lean_PersistentArray_push___redArg(v_traces_3603_, v___x_3614_);
if (v_isShared_3606_ == 0)
{
lean_ctor_set(v___x_3605_, 0, v___x_3615_);
v___x_3617_ = v___x_3605_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3615_);
lean_ctor_set_uint64(v_reuseFailAlloc_3626_, sizeof(void*)*1, v_tid_3602_);
v___x_3617_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
lean_object* v___x_3619_; 
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 4, v___x_3617_);
v___x_3619_ = v___x_3600_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_env_3591_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v_nextMacroScope_3592_);
lean_ctor_set(v_reuseFailAlloc_3625_, 2, v_ngen_3593_);
lean_ctor_set(v_reuseFailAlloc_3625_, 3, v_auxDeclNGen_3594_);
lean_ctor_set(v_reuseFailAlloc_3625_, 4, v___x_3617_);
lean_ctor_set(v_reuseFailAlloc_3625_, 5, v_cache_3595_);
lean_ctor_set(v_reuseFailAlloc_3625_, 6, v_messages_3596_);
lean_ctor_set(v_reuseFailAlloc_3625_, 7, v_infoState_3597_);
lean_ctor_set(v_reuseFailAlloc_3625_, 8, v_snapshotTasks_3598_);
v___x_3619_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3623_; 
v___x_3620_ = lean_st_ref_put(v___y_3581_, v___x_3619_);
v___x_3621_ = lean_box(0);
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 0, v___x_3621_);
v___x_3623_ = v___x_3587_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v___x_3621_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg___boxed(lean_object* v_cls_3630_, lean_object* v_msg_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
lean_object* v_res_3637_; 
v_res_3637_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v_cls_3630_, v_msg_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
return v_res_3637_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_reportIssue___closed__2(void){
_start:
{
lean_object* v___x_3641_; uint8_t v___x_3642_; double v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3641_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_3642_ = 1;
v___x_3643_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_3644_ = lean_box(0);
v___x_3645_ = ((lean_object*)(l_Lean_Meta_Sym_reportIssue___closed__1));
v___x_3646_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3646_, 0, v___x_3645_);
lean_ctor_set(v___x_3646_, 1, v___x_3644_);
lean_ctor_set(v___x_3646_, 2, v___x_3641_);
lean_ctor_set_float(v___x_3646_, sizeof(void*)*3, v___x_3643_);
lean_ctor_set_float(v___x_3646_, sizeof(void*)*3 + 8, v___x_3643_);
lean_ctor_set_uint8(v___x_3646_, sizeof(void*)*3 + 16, v___x_3642_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue(lean_object* v_msg_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_){
_start:
{
lean_object* v___x_3658_; lean_object* v_a_3659_; lean_object* v___x_3660_; lean_object* v_share_3661_; lean_object* v_maxFVar_3662_; lean_object* v_proofInstInfo_3663_; lean_object* v_inferType_3664_; lean_object* v_getLevel_3665_; lean_object* v_congrInfo_3666_; lean_object* v_defEqI_3667_; lean_object* v_extensions_3668_; lean_object* v_issues_3669_; lean_object* v_canon_3670_; lean_object* v_instanceOverrides_3671_; uint8_t v_debug_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3692_; 
v___x_3658_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3647_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_);
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
lean_inc(v_a_3659_);
lean_dec_ref(v___x_3658_);
v___x_3660_ = lean_st_ref_take(v_a_3649_);
v_share_3661_ = lean_ctor_get(v___x_3660_, 0);
v_maxFVar_3662_ = lean_ctor_get(v___x_3660_, 1);
v_proofInstInfo_3663_ = lean_ctor_get(v___x_3660_, 2);
v_inferType_3664_ = lean_ctor_get(v___x_3660_, 3);
v_getLevel_3665_ = lean_ctor_get(v___x_3660_, 4);
v_congrInfo_3666_ = lean_ctor_get(v___x_3660_, 5);
v_defEqI_3667_ = lean_ctor_get(v___x_3660_, 6);
v_extensions_3668_ = lean_ctor_get(v___x_3660_, 7);
v_issues_3669_ = lean_ctor_get(v___x_3660_, 8);
v_canon_3670_ = lean_ctor_get(v___x_3660_, 9);
v_instanceOverrides_3671_ = lean_ctor_get(v___x_3660_, 10);
v_debug_3672_ = lean_ctor_get_uint8(v___x_3660_, sizeof(void*)*11);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3674_ = v___x_3660_;
v_isShared_3675_ = v_isSharedCheck_3692_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_instanceOverrides_3671_);
lean_inc(v_canon_3670_);
lean_inc(v_issues_3669_);
lean_inc(v_extensions_3668_);
lean_inc(v_defEqI_3667_);
lean_inc(v_congrInfo_3666_);
lean_inc(v_getLevel_3665_);
lean_inc(v_inferType_3664_);
lean_inc(v_proofInstInfo_3663_);
lean_inc(v_maxFVar_3662_);
lean_inc(v_share_3661_);
lean_dec(v___x_3660_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3692_;
goto v_resetjp_3673_;
}
v___jp_3655_:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3656_ = lean_box(0);
v___x_3657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3656_);
return v___x_3657_;
}
v_resetjp_3673_:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3681_; 
v___x_3676_ = lean_obj_once(&l_Lean_Meta_Sym_reportIssue___closed__2, &l_Lean_Meta_Sym_reportIssue___closed__2_once, _init_l_Lean_Meta_Sym_reportIssue___closed__2);
v___x_3677_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
lean_inc(v_a_3659_);
v___x_3678_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3676_);
lean_ctor_set(v___x_3678_, 1, v_a_3659_);
lean_ctor_set(v___x_3678_, 2, v___x_3677_);
v___x_3679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3678_);
lean_ctor_set(v___x_3679_, 1, v_issues_3669_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 8, v___x_3679_);
v___x_3681_ = v___x_3674_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_share_3661_);
lean_ctor_set(v_reuseFailAlloc_3691_, 1, v_maxFVar_3662_);
lean_ctor_set(v_reuseFailAlloc_3691_, 2, v_proofInstInfo_3663_);
lean_ctor_set(v_reuseFailAlloc_3691_, 3, v_inferType_3664_);
lean_ctor_set(v_reuseFailAlloc_3691_, 4, v_getLevel_3665_);
lean_ctor_set(v_reuseFailAlloc_3691_, 5, v_congrInfo_3666_);
lean_ctor_set(v_reuseFailAlloc_3691_, 6, v_defEqI_3667_);
lean_ctor_set(v_reuseFailAlloc_3691_, 7, v_extensions_3668_);
lean_ctor_set(v_reuseFailAlloc_3691_, 8, v___x_3679_);
lean_ctor_set(v_reuseFailAlloc_3691_, 9, v_canon_3670_);
lean_ctor_set(v_reuseFailAlloc_3691_, 10, v_instanceOverrides_3671_);
lean_ctor_set_uint8(v_reuseFailAlloc_3691_, sizeof(void*)*11, v_debug_3672_);
v___x_3681_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
lean_object* v___x_3682_; lean_object* v_options_3683_; uint8_t v_hasTrace_3684_; 
v___x_3682_ = lean_st_ref_put(v_a_3649_, v___x_3681_);
v_options_3683_ = lean_ctor_get(v_a_3652_, 1);
v_hasTrace_3684_ = lean_ctor_get_uint8(v_options_3683_, sizeof(void*)*1);
if (v_hasTrace_3684_ == 0)
{
lean_dec(v_a_3659_);
goto v___jp_3655_;
}
else
{
lean_object* v_toCold_3685_; lean_object* v_inheritedTraceOptions_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; uint8_t v___x_3689_; 
v_toCold_3685_ = lean_ctor_get(v_a_3652_, 0);
v_inheritedTraceOptions_3686_ = lean_ctor_get(v_toCold_3685_, 4);
v___x_3687_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_3688_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__2);
v___x_3689_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3686_, v_options_3683_, v___x_3688_);
if (v___x_3689_ == 0)
{
lean_dec(v_a_3659_);
goto v___jp_3655_;
}
else
{
lean_object* v___x_3690_; 
v___x_3690_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v___x_3687_, v_a_3659_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_);
return v___x_3690_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue___boxed(lean_object* v_msg_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l_Lean_Meta_Sym_reportIssue(v_msg_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_);
lean_dec(v_a_3699_);
lean_dec_ref(v_a_3698_);
lean_dec(v_a_3697_);
lean_dec_ref(v_a_3696_);
lean_dec(v_a_3695_);
lean_dec_ref(v_a_3694_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0(lean_object* v_cls_3702_, lean_object* v_msg_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v___x_3711_; 
v___x_3711_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v_cls_3702_, v_msg_3703_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___boxed(lean_object* v_cls_3712_, lean_object* v_msg_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0(v_cls_3712_, v_msg_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_);
lean_dec(v___y_3719_);
lean_dec_ref(v___y_3718_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose(lean_object* v_msg_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_){
_start:
{
lean_object* v___x_3730_; lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3741_; 
v___x_3730_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3723_);
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3733_ = v___x_3730_;
v_isShared_3734_ = v_isSharedCheck_3741_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3730_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3741_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
uint8_t v_verbose_3735_; 
v_verbose_3735_ = lean_ctor_get_uint8(v_a_3731_, 0);
lean_dec(v_a_3731_);
if (v_verbose_3735_ == 0)
{
lean_object* v___x_3736_; lean_object* v___x_3738_; 
lean_dec_ref(v_msg_3722_);
v___x_3736_ = lean_box(0);
if (v_isShared_3734_ == 0)
{
lean_ctor_set(v___x_3733_, 0, v___x_3736_);
v___x_3738_ = v___x_3733_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3736_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
else
{
lean_object* v___x_3740_; 
lean_del_object(v___x_3733_);
v___x_3740_ = l_Lean_Meta_Sym_reportIssue(v_msg_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_);
return v___x_3740_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose___boxed(lean_object* v_msg_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_){
_start:
{
lean_object* v_res_3750_; 
v_res_3750_ = l_Lean_Meta_Sym_reportIssueIfVerbose(v_msg_3742_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_);
lean_dec(v_a_3748_);
lean_dec_ref(v_a_3747_);
lean_dec(v_a_3746_);
lean_dec_ref(v_a_3745_);
lean_dec(v_a_3744_);
lean_dec_ref(v_a_3743_);
return v_res_3750_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7(void){
_start:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; 
v___x_3766_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6));
v___x_3767_ = l_String_toRawSubstring_x27(v___x_3766_);
return v___x_3767_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24(void){
_start:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3805_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_3806_ = l_String_toRawSubstring_x27(v___x_3805_);
return v___x_3806_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30(void){
_start:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; 
v___x_3818_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29));
v___x_3819_ = l_String_toRawSubstring_x27(v___x_3818_);
return v___x_3819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(lean_object* v_s_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_){
_start:
{
lean_object* v_msg_3846_; lean_object* v_quotContext_3847_; lean_object* v_currMacroScope_3848_; lean_object* v_ref_3849_; lean_object* v___y_3850_; lean_object* v___x_3865_; lean_object* v___x_3866_; uint8_t v___x_3867_; 
lean_inc(v_s_3842_);
v___x_3865_ = l_Lean_Syntax_getKind(v_s_3842_);
v___x_3866_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16));
v___x_3867_ = lean_name_eq(v___x_3865_, v___x_3866_);
lean_dec(v___x_3865_);
if (v___x_3867_ == 0)
{
lean_object* v_quotContext_3868_; lean_object* v_currMacroScope_3869_; lean_object* v_ref_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v_quotContext_3868_ = lean_ctor_get(v_a_3843_, 1);
v_currMacroScope_3869_ = lean_ctor_get(v_a_3843_, 2);
v_ref_3870_ = lean_ctor_get(v_a_3843_, 5);
v___x_3871_ = l_Lean_SourceInfo_fromRef(v_ref_3870_, v___x_3867_);
v___x_3872_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18));
v___x_3873_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20));
v___x_3874_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21));
lean_inc_n(v___x_3871_, 8);
v___x_3875_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3871_);
lean_ctor_set(v___x_3875_, 1, v___x_3874_);
v___x_3876_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23));
v___x_3877_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
v___x_3878_ = lean_box(0);
lean_inc_n(v_currMacroScope_3869_, 3);
lean_inc_n(v_quotContext_3868_, 3);
v___x_3879_ = l_Lean_addMacroScope(v_quotContext_3868_, v___x_3878_, v_currMacroScope_3869_);
v___x_3880_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27));
v___x_3881_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3871_);
lean_ctor_set(v___x_3881_, 1, v___x_3877_);
lean_ctor_set(v___x_3881_, 2, v___x_3879_);
lean_ctor_set(v___x_3881_, 3, v___x_3880_);
v___x_3882_ = l_Lean_Syntax_node1(v___x_3871_, v___x_3876_, v___x_3881_);
v___x_3883_ = l_Lean_Syntax_node2(v___x_3871_, v___x_3873_, v___x_3875_, v___x_3882_);
v___x_3884_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28));
v___x_3885_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3871_);
lean_ctor_set(v___x_3885_, 1, v___x_3884_);
v___x_3886_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_3887_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
v___x_3888_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31));
v___x_3889_ = l_Lean_addMacroScope(v_quotContext_3868_, v___x_3888_, v_currMacroScope_3869_);
v___x_3890_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36));
v___x_3891_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3871_);
lean_ctor_set(v___x_3891_, 1, v___x_3887_);
lean_ctor_set(v___x_3891_, 2, v___x_3889_);
lean_ctor_set(v___x_3891_, 3, v___x_3890_);
v___x_3892_ = l_Lean_Syntax_node1(v___x_3871_, v___x_3886_, v___x_3891_);
v___x_3893_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37));
v___x_3894_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3871_);
lean_ctor_set(v___x_3894_, 1, v___x_3893_);
v___x_3895_ = l_Lean_Syntax_node5(v___x_3871_, v___x_3872_, v___x_3883_, v_s_3842_, v___x_3885_, v___x_3892_, v___x_3894_);
v_msg_3846_ = v___x_3895_;
v_quotContext_3847_ = v_quotContext_3868_;
v_currMacroScope_3848_ = v_currMacroScope_3869_;
v_ref_3849_ = v_ref_3870_;
v___y_3850_ = v_a_3844_;
goto v___jp_3845_;
}
else
{
lean_object* v_quotContext_3896_; lean_object* v_currMacroScope_3897_; lean_object* v_ref_3898_; uint8_t v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v_quotContext_3896_ = lean_ctor_get(v_a_3843_, 1);
v_currMacroScope_3897_ = lean_ctor_get(v_a_3843_, 2);
v_ref_3898_ = lean_ctor_get(v_a_3843_, 5);
v___x_3899_ = 0;
v___x_3900_ = l_Lean_SourceInfo_fromRef(v_ref_3898_, v___x_3899_);
v___x_3901_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39));
v___x_3902_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40));
lean_inc(v___x_3900_);
v___x_3903_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3900_);
lean_ctor_set(v___x_3903_, 1, v___x_3902_);
v___x_3904_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3901_, v___x_3903_, v_s_3842_);
lean_inc(v_currMacroScope_3897_);
lean_inc(v_quotContext_3896_);
v_msg_3846_ = v___x_3904_;
v_quotContext_3847_ = v_quotContext_3896_;
v_currMacroScope_3848_ = v_currMacroScope_3897_;
v_ref_3849_ = v_ref_3898_;
v___y_3850_ = v_a_3844_;
goto v___jp_3845_;
}
v___jp_3845_:
{
uint8_t v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3851_ = 0;
v___x_3852_ = l_Lean_SourceInfo_fromRef(v_ref_3849_, v___x_3851_);
v___x_3853_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3));
v___x_3854_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5));
v___x_3855_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7);
v___x_3856_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9));
v___x_3857_ = l_Lean_addMacroScope(v_quotContext_3847_, v___x_3856_, v_currMacroScope_3848_);
v___x_3858_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12));
lean_inc_n(v___x_3852_, 3);
v___x_3859_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3852_);
lean_ctor_set(v___x_3859_, 1, v___x_3855_);
lean_ctor_set(v___x_3859_, 2, v___x_3857_);
lean_ctor_set(v___x_3859_, 3, v___x_3858_);
v___x_3860_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_3861_ = l_Lean_Syntax_node1(v___x_3852_, v___x_3860_, v_msg_3846_);
v___x_3862_ = l_Lean_Syntax_node2(v___x_3852_, v___x_3854_, v___x_3859_, v___x_3861_);
v___x_3863_ = l_Lean_Syntax_node1(v___x_3852_, v___x_3853_, v___x_3862_);
v___x_3864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3863_);
lean_ctor_set(v___x_3864_, 1, v___y_3850_);
return v___x_3864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___boxed(lean_object* v_s_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_){
_start:
{
lean_object* v_res_3908_; 
v_res_3908_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(v_s_3905_, v_a_3906_, v_a_3907_);
lean_dec_ref(v_a_3906_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(lean_object* v_x_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_){
_start:
{
lean_object* v___x_3952_; uint8_t v___x_3953_; 
v___x_3952_ = ((lean_object*)(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1));
lean_inc(v_x_3949_);
v___x_3953_ = l_Lean_Syntax_isOfKind(v_x_3949_, v___x_3952_);
if (v___x_3953_ == 0)
{
lean_object* v___x_3954_; lean_object* v___x_3955_; 
lean_dec(v_x_3949_);
v___x_3954_ = lean_box(1);
v___x_3955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3954_);
lean_ctor_set(v___x_3955_, 1, v_a_3951_);
return v___x_3955_;
}
else
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v_a_3959_; lean_object* v_a_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3967_; 
v___x_3956_ = lean_unsigned_to_nat(1u);
v___x_3957_ = l_Lean_Syntax_getArg(v_x_3949_, v___x_3956_);
lean_dec(v_x_3949_);
v___x_3958_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(v___x_3957_, v_a_3950_, v_a_3951_);
v_a_3959_ = lean_ctor_get(v___x_3958_, 0);
v_a_3960_ = lean_ctor_get(v___x_3958_, 1);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3962_ = v___x_3958_;
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_a_3960_);
lean_inc(v_a_3959_);
lean_dec(v___x_3958_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3965_; 
if (v_isShared_3963_ == 0)
{
v___x_3965_ = v___x_3962_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_a_3959_);
lean_ctor_set(v_reuseFailAlloc_3966_, 1, v_a_3960_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1___boxed(lean_object* v_x_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(v_x_3968_, v_a_3969_, v_a_3970_);
lean_dec_ref(v_a_3969_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue(lean_object* v_msg_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_){
_start:
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_4000_; 
v___x_3980_ = l_Lean_KVMap_instValueBool;
v___x_3981_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3973_);
v_a_3982_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3984_ = v___x_3981_;
v_isShared_3985_ = v_isSharedCheck_4000_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3981_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_4000_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
uint8_t v_verbose_3986_; 
v_verbose_3986_ = lean_ctor_get_uint8(v_a_3982_, 0);
lean_dec(v_a_3982_);
if (v_verbose_3986_ == 0)
{
lean_object* v___x_3987_; lean_object* v___x_3989_; 
lean_dec_ref(v_msg_3972_);
v___x_3987_ = lean_box(0);
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 0, v___x_3987_);
v___x_3989_ = v___x_3984_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v___x_3987_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
else
{
lean_object* v_options_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; uint8_t v___x_3994_; 
v_options_3991_ = lean_ctor_get(v_a_3977_, 1);
v___x_3992_ = l_Lean_Meta_Sym_sym_debug;
v___x_3993_ = l_Lean_Option_get___redArg(v___x_3980_, v_options_3991_, v___x_3992_);
v___x_3994_ = lean_unbox(v___x_3993_);
lean_dec(v___x_3993_);
if (v___x_3994_ == 0)
{
lean_object* v___x_3995_; lean_object* v___x_3997_; 
lean_dec_ref(v_msg_3972_);
v___x_3995_ = lean_box(0);
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 0, v___x_3995_);
v___x_3997_ = v___x_3984_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v___x_3995_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
else
{
lean_object* v___x_3999_; 
lean_del_object(v___x_3984_);
v___x_3999_ = l_Lean_Meta_Sym_reportIssue(v_msg_3972_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_);
return v___x_3999_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue___boxed(lean_object* v_msg_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_){
_start:
{
lean_object* v_res_4009_; 
v_res_4009_ = l_Lean_Meta_Sym_reportDbgIssue(v_msg_4001_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_);
lean_dec(v_a_4007_);
lean_dec_ref(v_a_4006_);
lean_dec(v_a_4005_);
lean_dec_ref(v_a_4004_);
lean_dec(v_a_4003_);
lean_dec_ref(v_a_4002_);
return v_res_4009_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1(void){
_start:
{
lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4011_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0));
v___x_4012_ = l_String_toRawSubstring_x27(v___x_4011_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro(lean_object* v_s_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_){
_start:
{
lean_object* v_msg_4032_; lean_object* v_quotContext_4033_; lean_object* v_currMacroScope_4034_; lean_object* v_ref_4035_; lean_object* v___y_4036_; lean_object* v___x_4051_; lean_object* v___x_4052_; uint8_t v___x_4053_; 
lean_inc(v_s_4028_);
v___x_4051_ = l_Lean_Syntax_getKind(v_s_4028_);
v___x_4052_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16));
v___x_4053_ = lean_name_eq(v___x_4051_, v___x_4052_);
lean_dec(v___x_4051_);
if (v___x_4053_ == 0)
{
lean_object* v_quotContext_4054_; lean_object* v_currMacroScope_4055_; lean_object* v_ref_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v_quotContext_4054_ = lean_ctor_get(v_a_4029_, 1);
v_currMacroScope_4055_ = lean_ctor_get(v_a_4029_, 2);
v_ref_4056_ = lean_ctor_get(v_a_4029_, 5);
v___x_4057_ = l_Lean_SourceInfo_fromRef(v_ref_4056_, v___x_4053_);
v___x_4058_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18));
v___x_4059_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20));
v___x_4060_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21));
lean_inc_n(v___x_4057_, 8);
v___x_4061_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4061_, 0, v___x_4057_);
lean_ctor_set(v___x_4061_, 1, v___x_4060_);
v___x_4062_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23));
v___x_4063_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
v___x_4064_ = lean_box(0);
lean_inc_n(v_currMacroScope_4055_, 3);
lean_inc_n(v_quotContext_4054_, 3);
v___x_4065_ = l_Lean_addMacroScope(v_quotContext_4054_, v___x_4064_, v_currMacroScope_4055_);
v___x_4066_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27));
v___x_4067_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4057_);
lean_ctor_set(v___x_4067_, 1, v___x_4063_);
lean_ctor_set(v___x_4067_, 2, v___x_4065_);
lean_ctor_set(v___x_4067_, 3, v___x_4066_);
v___x_4068_ = l_Lean_Syntax_node1(v___x_4057_, v___x_4062_, v___x_4067_);
v___x_4069_ = l_Lean_Syntax_node2(v___x_4057_, v___x_4059_, v___x_4061_, v___x_4068_);
v___x_4070_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28));
v___x_4071_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4071_, 0, v___x_4057_);
lean_ctor_set(v___x_4071_, 1, v___x_4070_);
v___x_4072_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4073_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
v___x_4074_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31));
v___x_4075_ = l_Lean_addMacroScope(v_quotContext_4054_, v___x_4074_, v_currMacroScope_4055_);
v___x_4076_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36));
v___x_4077_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4057_);
lean_ctor_set(v___x_4077_, 1, v___x_4073_);
lean_ctor_set(v___x_4077_, 2, v___x_4075_);
lean_ctor_set(v___x_4077_, 3, v___x_4076_);
v___x_4078_ = l_Lean_Syntax_node1(v___x_4057_, v___x_4072_, v___x_4077_);
v___x_4079_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37));
v___x_4080_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4057_);
lean_ctor_set(v___x_4080_, 1, v___x_4079_);
v___x_4081_ = l_Lean_Syntax_node5(v___x_4057_, v___x_4058_, v___x_4069_, v_s_4028_, v___x_4071_, v___x_4078_, v___x_4080_);
v_msg_4032_ = v___x_4081_;
v_quotContext_4033_ = v_quotContext_4054_;
v_currMacroScope_4034_ = v_currMacroScope_4055_;
v_ref_4035_ = v_ref_4056_;
v___y_4036_ = v_a_4030_;
goto v___jp_4031_;
}
else
{
lean_object* v_quotContext_4082_; lean_object* v_currMacroScope_4083_; lean_object* v_ref_4084_; uint8_t v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v_quotContext_4082_ = lean_ctor_get(v_a_4029_, 1);
v_currMacroScope_4083_ = lean_ctor_get(v_a_4029_, 2);
v_ref_4084_ = lean_ctor_get(v_a_4029_, 5);
v___x_4085_ = 0;
v___x_4086_ = l_Lean_SourceInfo_fromRef(v_ref_4084_, v___x_4085_);
v___x_4087_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39));
v___x_4088_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40));
lean_inc(v___x_4086_);
v___x_4089_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4086_);
lean_ctor_set(v___x_4089_, 1, v___x_4088_);
v___x_4090_ = l_Lean_Syntax_node2(v___x_4086_, v___x_4087_, v___x_4089_, v_s_4028_);
lean_inc(v_currMacroScope_4083_);
lean_inc(v_quotContext_4082_);
v_msg_4032_ = v___x_4090_;
v_quotContext_4033_ = v_quotContext_4082_;
v_currMacroScope_4034_ = v_currMacroScope_4083_;
v_ref_4035_ = v_ref_4084_;
v___y_4036_ = v_a_4030_;
goto v___jp_4031_;
}
v___jp_4031_:
{
uint8_t v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4037_ = 0;
v___x_4038_ = l_Lean_SourceInfo_fromRef(v_ref_4035_, v___x_4037_);
v___x_4039_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3));
v___x_4040_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5));
v___x_4041_ = lean_obj_once(&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1, &l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1_once, _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1);
v___x_4042_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3));
v___x_4043_ = l_Lean_addMacroScope(v_quotContext_4033_, v___x_4042_, v_currMacroScope_4034_);
v___x_4044_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6));
lean_inc_n(v___x_4038_, 3);
v___x_4045_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4038_);
lean_ctor_set(v___x_4045_, 1, v___x_4041_);
lean_ctor_set(v___x_4045_, 2, v___x_4043_);
lean_ctor_set(v___x_4045_, 3, v___x_4044_);
v___x_4046_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4047_ = l_Lean_Syntax_node1(v___x_4038_, v___x_4046_, v_msg_4032_);
v___x_4048_ = l_Lean_Syntax_node2(v___x_4038_, v___x_4040_, v___x_4045_, v___x_4047_);
v___x_4049_ = l_Lean_Syntax_node1(v___x_4038_, v___x_4039_, v___x_4048_);
v___x_4050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4049_);
lean_ctor_set(v___x_4050_, 1, v___y_4036_);
return v___x_4050_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___boxed(lean_object* v_s_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_){
_start:
{
lean_object* v_res_4094_; 
v_res_4094_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v_s_4091_, v_a_4092_, v_a_4093_);
lean_dec_ref(v_a_4092_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(lean_object* v_x_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_){
_start:
{
lean_object* v___x_4116_; uint8_t v___x_4117_; 
v___x_4116_ = ((lean_object*)(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1));
lean_inc(v_x_4113_);
v___x_4117_ = l_Lean_Syntax_isOfKind(v_x_4113_, v___x_4116_);
if (v___x_4117_ == 0)
{
lean_object* v___x_4118_; lean_object* v___x_4119_; 
lean_dec(v_x_4113_);
v___x_4118_ = lean_box(1);
v___x_4119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4119_, 0, v___x_4118_);
lean_ctor_set(v___x_4119_, 1, v_a_4115_);
return v___x_4119_;
}
else
{
lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v_a_4123_; lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4131_; 
v___x_4120_ = lean_unsigned_to_nat(1u);
v___x_4121_ = l_Lean_Syntax_getArg(v_x_4113_, v___x_4120_);
lean_dec(v_x_4113_);
v___x_4122_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v___x_4121_, v_a_4114_, v_a_4115_);
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
v_a_4124_ = lean_ctor_get(v___x_4122_, 1);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4126_ = v___x_4122_;
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_inc(v_a_4123_);
lean_dec(v___x_4122_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_a_4123_);
lean_ctor_set(v_reuseFailAlloc_4130_, 1, v_a_4124_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
return v___x_4129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1___boxed(lean_object* v_x_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_){
_start:
{
lean_object* v_res_4135_; 
v_res_4135_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(v_x_4132_, v_a_4133_, v_a_4134_);
lean_dec_ref(v_a_4133_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg(lean_object* v_a_4136_){
_start:
{
lean_object* v___x_4138_; lean_object* v_issues_4139_; lean_object* v___x_4140_; 
v___x_4138_ = lean_st_ref_get(v_a_4136_);
v_issues_4139_ = lean_ctor_get(v___x_4138_, 8);
lean_inc(v_issues_4139_);
lean_dec(v___x_4138_);
v___x_4140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4140_, 0, v_issues_4139_);
return v___x_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg___boxed(lean_object* v_a_4141_, lean_object* v_a_4142_){
_start:
{
lean_object* v_res_4143_; 
v_res_4143_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4141_);
lean_dec(v_a_4141_);
return v_res_4143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues(lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_){
_start:
{
lean_object* v___x_4151_; 
v___x_4151_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4145_);
return v___x_4151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___boxed(lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_){
_start:
{
lean_object* v_res_4159_; 
v_res_4159_ = l_Lean_Meta_Sym_getIssues(v_a_4152_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
lean_dec(v_a_4157_);
lean_dec_ref(v_a_4156_);
lean_dec(v_a_4155_);
lean_dec_ref(v_a_4154_);
lean_dec(v_a_4153_);
lean_dec_ref(v_a_4152_);
return v_res_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(lean_object* v_a_4160_, lean_object* v_issues_4161_, lean_object* v_a_x3f_4162_){
_start:
{
lean_object* v___x_4164_; lean_object* v_share_4165_; lean_object* v_maxFVar_4166_; lean_object* v_proofInstInfo_4167_; lean_object* v_inferType_4168_; lean_object* v_getLevel_4169_; lean_object* v_congrInfo_4170_; lean_object* v_defEqI_4171_; lean_object* v_extensions_4172_; lean_object* v_issues_4173_; lean_object* v_canon_4174_; lean_object* v_instanceOverrides_4175_; uint8_t v_debug_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4187_; 
v___x_4164_ = lean_st_ref_take(v_a_4160_);
v_share_4165_ = lean_ctor_get(v___x_4164_, 0);
v_maxFVar_4166_ = lean_ctor_get(v___x_4164_, 1);
v_proofInstInfo_4167_ = lean_ctor_get(v___x_4164_, 2);
v_inferType_4168_ = lean_ctor_get(v___x_4164_, 3);
v_getLevel_4169_ = lean_ctor_get(v___x_4164_, 4);
v_congrInfo_4170_ = lean_ctor_get(v___x_4164_, 5);
v_defEqI_4171_ = lean_ctor_get(v___x_4164_, 6);
v_extensions_4172_ = lean_ctor_get(v___x_4164_, 7);
v_issues_4173_ = lean_ctor_get(v___x_4164_, 8);
v_canon_4174_ = lean_ctor_get(v___x_4164_, 9);
v_instanceOverrides_4175_ = lean_ctor_get(v___x_4164_, 10);
v_debug_4176_ = lean_ctor_get_uint8(v___x_4164_, sizeof(void*)*11);
v_isSharedCheck_4187_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4178_ = v___x_4164_;
v_isShared_4179_ = v_isSharedCheck_4187_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_instanceOverrides_4175_);
lean_inc(v_canon_4174_);
lean_inc(v_issues_4173_);
lean_inc(v_extensions_4172_);
lean_inc(v_defEqI_4171_);
lean_inc(v_congrInfo_4170_);
lean_inc(v_getLevel_4169_);
lean_inc(v_inferType_4168_);
lean_inc(v_proofInstInfo_4167_);
lean_inc(v_maxFVar_4166_);
lean_inc(v_share_4165_);
lean_dec(v___x_4164_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4187_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4180_; lean_object* v___x_4182_; 
v___x_4180_ = l_List_appendTR___redArg(v_issues_4173_, v_issues_4161_);
if (v_isShared_4179_ == 0)
{
lean_ctor_set(v___x_4178_, 8, v___x_4180_);
v___x_4182_ = v___x_4178_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_share_4165_);
lean_ctor_set(v_reuseFailAlloc_4186_, 1, v_maxFVar_4166_);
lean_ctor_set(v_reuseFailAlloc_4186_, 2, v_proofInstInfo_4167_);
lean_ctor_set(v_reuseFailAlloc_4186_, 3, v_inferType_4168_);
lean_ctor_set(v_reuseFailAlloc_4186_, 4, v_getLevel_4169_);
lean_ctor_set(v_reuseFailAlloc_4186_, 5, v_congrInfo_4170_);
lean_ctor_set(v_reuseFailAlloc_4186_, 6, v_defEqI_4171_);
lean_ctor_set(v_reuseFailAlloc_4186_, 7, v_extensions_4172_);
lean_ctor_set(v_reuseFailAlloc_4186_, 8, v___x_4180_);
lean_ctor_set(v_reuseFailAlloc_4186_, 9, v_canon_4174_);
lean_ctor_set(v_reuseFailAlloc_4186_, 10, v_instanceOverrides_4175_);
lean_ctor_set_uint8(v_reuseFailAlloc_4186_, sizeof(void*)*11, v_debug_4176_);
v___x_4182_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; 
v___x_4183_ = lean_st_ref_put(v_a_4160_, v___x_4182_);
v___x_4184_ = lean_box(0);
v___x_4185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4184_);
return v___x_4185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0___boxed(lean_object* v_a_4188_, lean_object* v_issues_4189_, lean_object* v_a_x3f_4190_, lean_object* v___y_4191_){
_start:
{
lean_object* v_res_4192_; 
v_res_4192_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4188_, v_issues_4189_, v_a_x3f_4190_);
lean_dec(v_a_x3f_4190_);
lean_dec(v_a_4188_);
return v_res_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg(lean_object* v_x_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_){
_start:
{
lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v_share_4203_; lean_object* v_maxFVar_4204_; lean_object* v_proofInstInfo_4205_; lean_object* v_inferType_4206_; lean_object* v_getLevel_4207_; lean_object* v_congrInfo_4208_; lean_object* v_defEqI_4209_; lean_object* v_extensions_4210_; lean_object* v_canon_4211_; lean_object* v_instanceOverrides_4212_; uint8_t v_debug_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4252_; 
v___x_4201_ = lean_st_ref_get(v_a_4195_);
v___x_4202_ = lean_st_ref_take(v_a_4195_);
v_share_4203_ = lean_ctor_get(v___x_4202_, 0);
v_maxFVar_4204_ = lean_ctor_get(v___x_4202_, 1);
v_proofInstInfo_4205_ = lean_ctor_get(v___x_4202_, 2);
v_inferType_4206_ = lean_ctor_get(v___x_4202_, 3);
v_getLevel_4207_ = lean_ctor_get(v___x_4202_, 4);
v_congrInfo_4208_ = lean_ctor_get(v___x_4202_, 5);
v_defEqI_4209_ = lean_ctor_get(v___x_4202_, 6);
v_extensions_4210_ = lean_ctor_get(v___x_4202_, 7);
v_canon_4211_ = lean_ctor_get(v___x_4202_, 9);
v_instanceOverrides_4212_ = lean_ctor_get(v___x_4202_, 10);
v_debug_4213_ = lean_ctor_get_uint8(v___x_4202_, sizeof(void*)*11);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4202_);
if (v_isSharedCheck_4252_ == 0)
{
lean_object* v_unused_4253_; 
v_unused_4253_ = lean_ctor_get(v___x_4202_, 8);
lean_dec(v_unused_4253_);
v___x_4215_ = v___x_4202_;
v_isShared_4216_ = v_isSharedCheck_4252_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_instanceOverrides_4212_);
lean_inc(v_canon_4211_);
lean_inc(v_extensions_4210_);
lean_inc(v_defEqI_4209_);
lean_inc(v_congrInfo_4208_);
lean_inc(v_getLevel_4207_);
lean_inc(v_inferType_4206_);
lean_inc(v_proofInstInfo_4205_);
lean_inc(v_maxFVar_4204_);
lean_inc(v_share_4203_);
lean_dec(v___x_4202_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4252_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4217_; lean_object* v___x_4219_; 
v___x_4217_ = lean_box(0);
if (v_isShared_4216_ == 0)
{
lean_ctor_set(v___x_4215_, 8, v___x_4217_);
v___x_4219_ = v___x_4215_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v_share_4203_);
lean_ctor_set(v_reuseFailAlloc_4251_, 1, v_maxFVar_4204_);
lean_ctor_set(v_reuseFailAlloc_4251_, 2, v_proofInstInfo_4205_);
lean_ctor_set(v_reuseFailAlloc_4251_, 3, v_inferType_4206_);
lean_ctor_set(v_reuseFailAlloc_4251_, 4, v_getLevel_4207_);
lean_ctor_set(v_reuseFailAlloc_4251_, 5, v_congrInfo_4208_);
lean_ctor_set(v_reuseFailAlloc_4251_, 6, v_defEqI_4209_);
lean_ctor_set(v_reuseFailAlloc_4251_, 7, v_extensions_4210_);
lean_ctor_set(v_reuseFailAlloc_4251_, 8, v___x_4217_);
lean_ctor_set(v_reuseFailAlloc_4251_, 9, v_canon_4211_);
lean_ctor_set(v_reuseFailAlloc_4251_, 10, v_instanceOverrides_4212_);
lean_ctor_set_uint8(v_reuseFailAlloc_4251_, sizeof(void*)*11, v_debug_4213_);
v___x_4219_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
lean_object* v___x_4220_; lean_object* v_issues_4221_; lean_object* v_r_4222_; 
v___x_4220_ = lean_st_ref_put(v_a_4195_, v___x_4219_);
v_issues_4221_ = lean_ctor_get(v___x_4201_, 8);
lean_inc(v_issues_4221_);
lean_dec(v___x_4201_);
lean_inc(v_a_4199_);
lean_inc_ref(v_a_4198_);
lean_inc(v_a_4197_);
lean_inc_ref(v_a_4196_);
lean_inc(v_a_4195_);
lean_inc_ref(v_a_4194_);
v_r_4222_ = lean_apply_7(v_x_4193_, v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_, lean_box(0));
if (lean_obj_tag(v_r_4222_) == 0)
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4239_; 
v_a_4223_ = lean_ctor_get(v_r_4222_, 0);
v_isSharedCheck_4239_ = !lean_is_exclusive(v_r_4222_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4225_ = v_r_4222_;
v_isShared_4226_ = v_isSharedCheck_4239_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v_r_4222_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4239_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4228_; 
lean_inc(v_a_4223_);
if (v_isShared_4226_ == 0)
{
lean_ctor_set_tag(v___x_4225_, 1);
v___x_4228_ = v___x_4225_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_a_4223_);
v___x_4228_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
lean_object* v___x_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4236_; 
v___x_4229_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4195_, v_issues_4221_, v___x_4228_);
lean_dec_ref(v___x_4228_);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4236_ == 0)
{
lean_object* v_unused_4237_; 
v_unused_4237_ = lean_ctor_get(v___x_4229_, 0);
lean_dec(v_unused_4237_);
v___x_4231_ = v___x_4229_;
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
else
{
lean_dec(v___x_4229_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4234_; 
if (v_isShared_4232_ == 0)
{
lean_ctor_set(v___x_4231_, 0, v_a_4223_);
v___x_4234_ = v___x_4231_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_a_4223_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
}
else
{
lean_object* v_a_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4249_; 
v_a_4240_ = lean_ctor_get(v_r_4222_, 0);
lean_inc(v_a_4240_);
lean_dec_ref_known(v_r_4222_, 1);
v___x_4241_ = lean_box(0);
v___x_4242_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4195_, v_issues_4221_, v___x_4241_);
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4242_);
if (v_isSharedCheck_4249_ == 0)
{
lean_object* v_unused_4250_; 
v_unused_4250_ = lean_ctor_get(v___x_4242_, 0);
lean_dec(v_unused_4250_);
v___x_4244_ = v___x_4242_;
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
else
{
lean_dec(v___x_4242_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4247_; 
if (v_isShared_4245_ == 0)
{
lean_ctor_set_tag(v___x_4244_, 1);
lean_ctor_set(v___x_4244_, 0, v_a_4240_);
v___x_4247_ = v___x_4244_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_a_4240_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___boxed(lean_object* v_x_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_){
_start:
{
lean_object* v_res_4262_; 
v_res_4262_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_, v_a_4260_);
lean_dec(v_a_4260_);
lean_dec_ref(v_a_4259_);
lean_dec(v_a_4258_);
lean_dec_ref(v_a_4257_);
lean_dec(v_a_4256_);
lean_dec_ref(v_a_4255_);
return v_res_4262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext(lean_object* v_00_u03b1_4263_, lean_object* v_x_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_){
_start:
{
lean_object* v___x_4272_; 
v___x_4272_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_4264_, v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___boxed(lean_object* v_00_u03b1_4273_, lean_object* v_x_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_){
_start:
{
lean_object* v_res_4282_; 
v_res_4282_ = l_Lean_Meta_Sym_withNewIssueContext(v_00_u03b1_4273_, v_x_4274_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_);
lean_dec(v_a_4280_);
lean_dec_ref(v_a_4279_);
lean_dec(v_a_4278_);
lean_dec_ref(v_a_4277_);
lean_dec(v_a_4276_);
lean_dec_ref(v_a_4275_);
return v_res_4282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4283_, lean_object* v_vals_4284_, lean_object* v_i_4285_, lean_object* v_k_4286_){
_start:
{
lean_object* v___x_4291_; uint8_t v___x_4292_; 
v___x_4291_ = lean_array_get_size(v_keys_4283_);
v___x_4292_ = lean_nat_dec_lt(v_i_4285_, v___x_4291_);
if (v___x_4292_ == 0)
{
lean_object* v___x_4293_; 
lean_dec(v_i_4285_);
v___x_4293_ = lean_box(0);
return v___x_4293_;
}
else
{
lean_object* v_fst_4294_; lean_object* v_snd_4295_; lean_object* v_k_x27_4296_; lean_object* v_fst_4297_; lean_object* v_snd_4298_; size_t v___x_4299_; size_t v___x_4300_; uint8_t v___x_4301_; 
v_fst_4294_ = lean_ctor_get(v_k_4286_, 0);
v_snd_4295_ = lean_ctor_get(v_k_4286_, 1);
v_k_x27_4296_ = lean_array_fget_borrowed(v_keys_4283_, v_i_4285_);
v_fst_4297_ = lean_ctor_get(v_k_x27_4296_, 0);
v_snd_4298_ = lean_ctor_get(v_k_x27_4296_, 1);
v___x_4299_ = lean_ptr_addr(v_fst_4294_);
v___x_4300_ = lean_ptr_addr(v_fst_4297_);
v___x_4301_ = lean_usize_dec_eq(v___x_4299_, v___x_4300_);
if (v___x_4301_ == 0)
{
goto v___jp_4287_;
}
else
{
size_t v___x_4302_; size_t v___x_4303_; uint8_t v___x_4304_; 
v___x_4302_ = lean_ptr_addr(v_snd_4295_);
v___x_4303_ = lean_ptr_addr(v_snd_4298_);
v___x_4304_ = lean_usize_dec_eq(v___x_4302_, v___x_4303_);
if (v___x_4304_ == 0)
{
goto v___jp_4287_;
}
else
{
lean_object* v___x_4305_; lean_object* v___x_4306_; 
v___x_4305_ = lean_array_fget_borrowed(v_vals_4284_, v_i_4285_);
lean_dec(v_i_4285_);
lean_inc(v___x_4305_);
v___x_4306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4305_);
return v___x_4306_;
}
}
}
v___jp_4287_:
{
lean_object* v___x_4288_; lean_object* v___x_4289_; 
v___x_4288_ = lean_unsigned_to_nat(1u);
v___x_4289_ = lean_nat_add(v_i_4285_, v___x_4288_);
lean_dec(v_i_4285_);
v_i_4285_ = v___x_4289_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4307_, lean_object* v_vals_4308_, lean_object* v_i_4309_, lean_object* v_k_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_4307_, v_vals_4308_, v_i_4309_, v_k_4310_);
lean_dec_ref(v_k_4310_);
lean_dec_ref(v_vals_4308_);
lean_dec_ref(v_keys_4307_);
return v_res_4311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(lean_object* v_x_4312_, size_t v_x_4313_, lean_object* v_x_4314_){
_start:
{
if (lean_obj_tag(v_x_4312_) == 0)
{
lean_object* v_es_4315_; lean_object* v___x_4316_; size_t v___x_4317_; size_t v___x_4318_; lean_object* v_j_4319_; lean_object* v___x_4320_; 
v_es_4315_ = lean_ctor_get(v_x_4312_, 0);
v___x_4316_ = lean_box(2);
v___x_4317_ = ((size_t)31ULL);
v___x_4318_ = lean_usize_land(v_x_4313_, v___x_4317_);
v_j_4319_ = lean_usize_to_nat(v___x_4318_);
v___x_4320_ = lean_array_get_borrowed(v___x_4316_, v_es_4315_, v_j_4319_);
lean_dec(v_j_4319_);
switch(lean_obj_tag(v___x_4320_))
{
case 0:
{
lean_object* v_key_4321_; lean_object* v_val_4322_; lean_object* v_fst_4323_; lean_object* v_snd_4324_; lean_object* v_fst_4325_; lean_object* v_snd_4326_; size_t v___x_4327_; size_t v___x_4328_; uint8_t v___x_4329_; 
v_key_4321_ = lean_ctor_get(v___x_4320_, 0);
v_val_4322_ = lean_ctor_get(v___x_4320_, 1);
v_fst_4323_ = lean_ctor_get(v_x_4314_, 0);
v_snd_4324_ = lean_ctor_get(v_x_4314_, 1);
v_fst_4325_ = lean_ctor_get(v_key_4321_, 0);
v_snd_4326_ = lean_ctor_get(v_key_4321_, 1);
v___x_4327_ = lean_ptr_addr(v_fst_4323_);
v___x_4328_ = lean_ptr_addr(v_fst_4325_);
v___x_4329_ = lean_usize_dec_eq(v___x_4327_, v___x_4328_);
if (v___x_4329_ == 0)
{
lean_object* v___x_4330_; 
v___x_4330_ = lean_box(0);
return v___x_4330_;
}
else
{
size_t v___x_4331_; size_t v___x_4332_; uint8_t v___x_4333_; 
v___x_4331_ = lean_ptr_addr(v_snd_4324_);
v___x_4332_ = lean_ptr_addr(v_snd_4326_);
v___x_4333_ = lean_usize_dec_eq(v___x_4331_, v___x_4332_);
if (v___x_4333_ == 0)
{
lean_object* v___x_4334_; 
v___x_4334_ = lean_box(0);
return v___x_4334_;
}
else
{
lean_object* v___x_4335_; 
lean_inc(v_val_4322_);
v___x_4335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4335_, 0, v_val_4322_);
return v___x_4335_;
}
}
}
case 1:
{
lean_object* v_node_4336_; size_t v___x_4337_; size_t v___x_4338_; 
v_node_4336_ = lean_ctor_get(v___x_4320_, 0);
v___x_4337_ = ((size_t)5ULL);
v___x_4338_ = lean_usize_shift_right(v_x_4313_, v___x_4337_);
v_x_4312_ = v_node_4336_;
v_x_4313_ = v___x_4338_;
goto _start;
}
default: 
{
lean_object* v___x_4340_; 
v___x_4340_ = lean_box(0);
return v___x_4340_;
}
}
}
else
{
lean_object* v_ks_4341_; lean_object* v_vs_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; 
v_ks_4341_ = lean_ctor_get(v_x_4312_, 0);
v_vs_4342_ = lean_ctor_get(v_x_4312_, 1);
v___x_4343_ = lean_unsigned_to_nat(0u);
v___x_4344_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_ks_4341_, v_vs_4342_, v___x_4343_, v_x_4314_);
return v___x_4344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg___boxed(lean_object* v_x_4345_, lean_object* v_x_4346_, lean_object* v_x_4347_){
_start:
{
size_t v_x_2860__boxed_4348_; lean_object* v_res_4349_; 
v_x_2860__boxed_4348_ = lean_unbox_usize(v_x_4346_);
lean_dec(v_x_4346_);
v_res_4349_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4345_, v_x_2860__boxed_4348_, v_x_4347_);
lean_dec_ref(v_x_4347_);
lean_dec_ref(v_x_4345_);
return v_res_4349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(lean_object* v_x_4350_, lean_object* v_x_4351_){
_start:
{
lean_object* v_fst_4352_; lean_object* v_snd_4353_; size_t v___x_4354_; size_t v___x_4355_; size_t v___x_4356_; uint64_t v___x_4357_; size_t v___x_4358_; size_t v___x_4359_; uint64_t v___x_4360_; uint64_t v___x_4361_; size_t v___x_4362_; lean_object* v___x_4363_; 
v_fst_4352_ = lean_ctor_get(v_x_4351_, 0);
v_snd_4353_ = lean_ctor_get(v_x_4351_, 1);
v___x_4354_ = lean_ptr_addr(v_fst_4352_);
v___x_4355_ = ((size_t)3ULL);
v___x_4356_ = lean_usize_shift_right(v___x_4354_, v___x_4355_);
v___x_4357_ = lean_usize_to_uint64(v___x_4356_);
v___x_4358_ = lean_ptr_addr(v_snd_4353_);
v___x_4359_ = lean_usize_shift_right(v___x_4358_, v___x_4355_);
v___x_4360_ = lean_usize_to_uint64(v___x_4359_);
v___x_4361_ = lean_uint64_mix_hash(v___x_4357_, v___x_4360_);
v___x_4362_ = lean_uint64_to_usize(v___x_4361_);
v___x_4363_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4350_, v___x_4362_, v_x_4351_);
return v___x_4363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg___boxed(lean_object* v_x_4364_, lean_object* v_x_4365_){
_start:
{
lean_object* v_res_4366_; 
v_res_4366_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_4364_, v_x_4365_);
lean_dec_ref(v_x_4365_);
lean_dec_ref(v_x_4364_);
return v_res_4366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_4367_, lean_object* v_x_4368_, lean_object* v_x_4369_, lean_object* v_x_4370_){
_start:
{
lean_object* v_ks_4371_; lean_object* v_vs_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4408_; 
v_ks_4371_ = lean_ctor_get(v_x_4367_, 0);
v_vs_4372_ = lean_ctor_get(v_x_4367_, 1);
v_isSharedCheck_4408_ = !lean_is_exclusive(v_x_4367_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4374_ = v_x_4367_;
v_isShared_4375_ = v_isSharedCheck_4408_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_vs_4372_);
lean_inc(v_ks_4371_);
lean_dec(v_x_4367_);
v___x_4374_ = lean_box(0);
v_isShared_4375_ = v_isSharedCheck_4408_;
goto v_resetjp_4373_;
}
v_resetjp_4373_:
{
lean_object* v___x_4383_; uint8_t v___x_4384_; 
v___x_4383_ = lean_array_get_size(v_ks_4371_);
v___x_4384_ = lean_nat_dec_lt(v_x_4368_, v___x_4383_);
if (v___x_4384_ == 0)
{
lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; 
lean_del_object(v___x_4374_);
lean_dec(v_x_4368_);
v___x_4385_ = lean_array_push(v_ks_4371_, v_x_4369_);
v___x_4386_ = lean_array_push(v_vs_4372_, v_x_4370_);
v___x_4387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4387_, 0, v___x_4385_);
lean_ctor_set(v___x_4387_, 1, v___x_4386_);
return v___x_4387_;
}
else
{
lean_object* v_fst_4388_; lean_object* v_snd_4389_; lean_object* v_k_x27_4390_; lean_object* v_fst_4391_; lean_object* v_snd_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4407_; 
v_fst_4388_ = lean_ctor_get(v_x_4369_, 0);
v_snd_4389_ = lean_ctor_get(v_x_4369_, 1);
v_k_x27_4390_ = lean_array_fget(v_ks_4371_, v_x_4368_);
v_fst_4391_ = lean_ctor_get(v_k_x27_4390_, 0);
v_snd_4392_ = lean_ctor_get(v_k_x27_4390_, 1);
v_isSharedCheck_4407_ = !lean_is_exclusive(v_k_x27_4390_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4394_ = v_k_x27_4390_;
v_isShared_4395_ = v_isSharedCheck_4407_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_snd_4392_);
lean_inc(v_fst_4391_);
lean_dec(v_k_x27_4390_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4407_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
size_t v___x_4396_; size_t v___x_4397_; uint8_t v___x_4398_; 
v___x_4396_ = lean_ptr_addr(v_fst_4388_);
v___x_4397_ = lean_ptr_addr(v_fst_4391_);
lean_dec(v_fst_4391_);
v___x_4398_ = lean_usize_dec_eq(v___x_4396_, v___x_4397_);
if (v___x_4398_ == 0)
{
lean_del_object(v___x_4394_);
lean_dec(v_snd_4392_);
goto v___jp_4376_;
}
else
{
size_t v___x_4399_; size_t v___x_4400_; uint8_t v___x_4401_; 
v___x_4399_ = lean_ptr_addr(v_snd_4389_);
v___x_4400_ = lean_ptr_addr(v_snd_4392_);
lean_dec(v_snd_4392_);
v___x_4401_ = lean_usize_dec_eq(v___x_4399_, v___x_4400_);
if (v___x_4401_ == 0)
{
lean_del_object(v___x_4394_);
goto v___jp_4376_;
}
else
{
lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4405_; 
lean_del_object(v___x_4374_);
v___x_4402_ = lean_array_fset(v_ks_4371_, v_x_4368_, v_x_4369_);
v___x_4403_ = lean_array_fset(v_vs_4372_, v_x_4368_, v_x_4370_);
lean_dec(v_x_4368_);
if (v_isShared_4395_ == 0)
{
lean_ctor_set_tag(v___x_4394_, 1);
lean_ctor_set(v___x_4394_, 1, v___x_4403_);
lean_ctor_set(v___x_4394_, 0, v___x_4402_);
v___x_4405_ = v___x_4394_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v___x_4402_);
lean_ctor_set(v_reuseFailAlloc_4406_, 1, v___x_4403_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
return v___x_4405_;
}
}
}
}
}
v___jp_4376_:
{
lean_object* v___x_4378_; 
if (v_isShared_4375_ == 0)
{
v___x_4378_ = v___x_4374_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_ks_4371_);
lean_ctor_set(v_reuseFailAlloc_4382_, 1, v_vs_4372_);
v___x_4378_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; 
v___x_4379_ = lean_unsigned_to_nat(1u);
v___x_4380_ = lean_nat_add(v_x_4368_, v___x_4379_);
lean_dec(v_x_4368_);
v_x_4367_ = v___x_4378_;
v_x_4368_ = v___x_4380_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(lean_object* v_n_4409_, lean_object* v_k_4410_, lean_object* v_v_4411_){
_start:
{
lean_object* v___x_4412_; lean_object* v___x_4413_; 
v___x_4412_ = lean_unsigned_to_nat(0u);
v___x_4413_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_n_4409_, v___x_4412_, v_k_4410_, v_v_4411_);
return v___x_4413_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4414_; 
v___x_4414_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4414_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(lean_object* v_x_4415_, size_t v_x_4416_, size_t v_x_4417_, lean_object* v_x_4418_, lean_object* v_x_4419_){
_start:
{
if (lean_obj_tag(v_x_4415_) == 0)
{
lean_object* v_es_4420_; size_t v___x_4421_; size_t v___x_4422_; lean_object* v_j_4423_; lean_object* v___x_4424_; uint8_t v___x_4425_; 
v_es_4420_ = lean_ctor_get(v_x_4415_, 0);
v___x_4421_ = ((size_t)31ULL);
v___x_4422_ = lean_usize_land(v_x_4416_, v___x_4421_);
v_j_4423_ = lean_usize_to_nat(v___x_4422_);
v___x_4424_ = lean_array_get_size(v_es_4420_);
v___x_4425_ = lean_nat_dec_lt(v_j_4423_, v___x_4424_);
if (v___x_4425_ == 0)
{
lean_dec(v_j_4423_);
lean_dec(v_x_4419_);
lean_dec_ref(v_x_4418_);
return v_x_4415_;
}
else
{
lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4474_; 
lean_inc_ref(v_es_4420_);
v_isSharedCheck_4474_ = !lean_is_exclusive(v_x_4415_);
if (v_isSharedCheck_4474_ == 0)
{
lean_object* v_unused_4475_; 
v_unused_4475_ = lean_ctor_get(v_x_4415_, 0);
lean_dec(v_unused_4475_);
v___x_4427_ = v_x_4415_;
v_isShared_4428_ = v_isSharedCheck_4474_;
goto v_resetjp_4426_;
}
else
{
lean_dec(v_x_4415_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4474_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v_v_4429_; lean_object* v___x_4430_; lean_object* v_xs_x27_4431_; lean_object* v___y_4433_; 
v_v_4429_ = lean_array_fget(v_es_4420_, v_j_4423_);
v___x_4430_ = lean_box(0);
v_xs_x27_4431_ = lean_array_fset(v_es_4420_, v_j_4423_, v___x_4430_);
switch(lean_obj_tag(v_v_4429_))
{
case 0:
{
lean_object* v_key_4438_; lean_object* v_val_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4459_; 
v_key_4438_ = lean_ctor_get(v_v_4429_, 0);
v_val_4439_ = lean_ctor_get(v_v_4429_, 1);
v_isSharedCheck_4459_ = !lean_is_exclusive(v_v_4429_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4441_ = v_v_4429_;
v_isShared_4442_ = v_isSharedCheck_4459_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_val_4439_);
lean_inc(v_key_4438_);
lean_dec(v_v_4429_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4459_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v_fst_4446_; lean_object* v_snd_4447_; lean_object* v_fst_4448_; lean_object* v_snd_4449_; size_t v___x_4450_; size_t v___x_4451_; uint8_t v___x_4452_; 
v_fst_4446_ = lean_ctor_get(v_x_4418_, 0);
v_snd_4447_ = lean_ctor_get(v_x_4418_, 1);
v_fst_4448_ = lean_ctor_get(v_key_4438_, 0);
v_snd_4449_ = lean_ctor_get(v_key_4438_, 1);
v___x_4450_ = lean_ptr_addr(v_fst_4446_);
v___x_4451_ = lean_ptr_addr(v_fst_4448_);
v___x_4452_ = lean_usize_dec_eq(v___x_4450_, v___x_4451_);
if (v___x_4452_ == 0)
{
lean_del_object(v___x_4441_);
goto v___jp_4443_;
}
else
{
size_t v___x_4453_; size_t v___x_4454_; uint8_t v___x_4455_; 
v___x_4453_ = lean_ptr_addr(v_snd_4447_);
v___x_4454_ = lean_ptr_addr(v_snd_4449_);
v___x_4455_ = lean_usize_dec_eq(v___x_4453_, v___x_4454_);
if (v___x_4455_ == 0)
{
lean_del_object(v___x_4441_);
goto v___jp_4443_;
}
else
{
lean_object* v___x_4457_; 
lean_dec(v_val_4439_);
lean_dec(v_key_4438_);
if (v_isShared_4442_ == 0)
{
lean_ctor_set(v___x_4441_, 1, v_x_4419_);
lean_ctor_set(v___x_4441_, 0, v_x_4418_);
v___x_4457_ = v___x_4441_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v_x_4418_);
lean_ctor_set(v_reuseFailAlloc_4458_, 1, v_x_4419_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
v___y_4433_ = v___x_4457_;
goto v___jp_4432_;
}
}
}
v___jp_4443_:
{
lean_object* v___x_4444_; lean_object* v___x_4445_; 
v___x_4444_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4438_, v_val_4439_, v_x_4418_, v_x_4419_);
v___x_4445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4445_, 0, v___x_4444_);
v___y_4433_ = v___x_4445_;
goto v___jp_4432_;
}
}
}
case 1:
{
lean_object* v_node_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4472_; 
v_node_4460_ = lean_ctor_get(v_v_4429_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v_v_4429_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4462_ = v_v_4429_;
v_isShared_4463_ = v_isSharedCheck_4472_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_node_4460_);
lean_dec(v_v_4429_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4472_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
size_t v___x_4464_; size_t v___x_4465_; size_t v___x_4466_; size_t v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4470_; 
v___x_4464_ = ((size_t)5ULL);
v___x_4465_ = lean_usize_shift_right(v_x_4416_, v___x_4464_);
v___x_4466_ = ((size_t)1ULL);
v___x_4467_ = lean_usize_add(v_x_4417_, v___x_4466_);
v___x_4468_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_node_4460_, v___x_4465_, v___x_4467_, v_x_4418_, v_x_4419_);
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 0, v___x_4468_);
v___x_4470_ = v___x_4462_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4468_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
v___y_4433_ = v___x_4470_;
goto v___jp_4432_;
}
}
}
default: 
{
lean_object* v___x_4473_; 
v___x_4473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4473_, 0, v_x_4418_);
lean_ctor_set(v___x_4473_, 1, v_x_4419_);
v___y_4433_ = v___x_4473_;
goto v___jp_4432_;
}
}
v___jp_4432_:
{
lean_object* v___x_4434_; lean_object* v___x_4436_; 
v___x_4434_ = lean_array_fset(v_xs_x27_4431_, v_j_4423_, v___y_4433_);
lean_dec(v_j_4423_);
if (v_isShared_4428_ == 0)
{
lean_ctor_set(v___x_4427_, 0, v___x_4434_);
v___x_4436_ = v___x_4427_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v___x_4434_);
v___x_4436_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
return v___x_4436_;
}
}
}
}
}
else
{
lean_object* v_ks_4476_; lean_object* v_vs_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4495_; 
v_ks_4476_ = lean_ctor_get(v_x_4415_, 0);
v_vs_4477_ = lean_ctor_get(v_x_4415_, 1);
v_isSharedCheck_4495_ = !lean_is_exclusive(v_x_4415_);
if (v_isSharedCheck_4495_ == 0)
{
v___x_4479_ = v_x_4415_;
v_isShared_4480_ = v_isSharedCheck_4495_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_vs_4477_);
lean_inc(v_ks_4476_);
lean_dec(v_x_4415_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4495_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4482_; 
if (v_isShared_4480_ == 0)
{
v___x_4482_ = v___x_4479_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v_ks_4476_);
lean_ctor_set(v_reuseFailAlloc_4494_, 1, v_vs_4477_);
v___x_4482_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
lean_object* v_newNode_4483_; size_t v___x_4484_; uint8_t v___x_4485_; 
v_newNode_4483_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v___x_4482_, v_x_4418_, v_x_4419_);
v___x_4484_ = ((size_t)7ULL);
v___x_4485_ = lean_usize_dec_le(v___x_4484_, v_x_4417_);
if (v___x_4485_ == 0)
{
lean_object* v___x_4486_; lean_object* v___x_4487_; uint8_t v___x_4488_; 
v___x_4486_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4483_);
v___x_4487_ = lean_unsigned_to_nat(4u);
v___x_4488_ = lean_nat_dec_lt(v___x_4486_, v___x_4487_);
lean_dec(v___x_4486_);
if (v___x_4488_ == 0)
{
lean_object* v_ks_4489_; lean_object* v_vs_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; 
v_ks_4489_ = lean_ctor_get(v_newNode_4483_, 0);
lean_inc_ref(v_ks_4489_);
v_vs_4490_ = lean_ctor_get(v_newNode_4483_, 1);
lean_inc_ref(v_vs_4490_);
lean_dec_ref(v_newNode_4483_);
v___x_4491_ = lean_unsigned_to_nat(0u);
v___x_4492_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0);
v___x_4493_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_x_4417_, v_ks_4489_, v_vs_4490_, v___x_4491_, v___x_4492_);
lean_dec_ref(v_vs_4490_);
lean_dec_ref(v_ks_4489_);
return v___x_4493_;
}
else
{
return v_newNode_4483_;
}
}
else
{
return v_newNode_4483_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(size_t v_depth_4496_, lean_object* v_keys_4497_, lean_object* v_vals_4498_, lean_object* v_i_4499_, lean_object* v_entries_4500_){
_start:
{
lean_object* v___x_4501_; uint8_t v___x_4502_; 
v___x_4501_ = lean_array_get_size(v_keys_4497_);
v___x_4502_ = lean_nat_dec_lt(v_i_4499_, v___x_4501_);
if (v___x_4502_ == 0)
{
lean_dec(v_i_4499_);
return v_entries_4500_;
}
else
{
lean_object* v_k_4503_; lean_object* v_fst_4504_; lean_object* v_snd_4505_; lean_object* v_v_4506_; size_t v___x_4507_; size_t v___x_4508_; size_t v___x_4509_; uint64_t v___x_4510_; size_t v___x_4511_; size_t v___x_4512_; uint64_t v___x_4513_; uint64_t v___x_4514_; size_t v_h_4515_; size_t v___x_4516_; lean_object* v___x_4517_; size_t v___x_4518_; size_t v___x_4519_; size_t v___x_4520_; size_t v_h_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; 
v_k_4503_ = lean_array_fget_borrowed(v_keys_4497_, v_i_4499_);
v_fst_4504_ = lean_ctor_get(v_k_4503_, 0);
v_snd_4505_ = lean_ctor_get(v_k_4503_, 1);
v_v_4506_ = lean_array_fget_borrowed(v_vals_4498_, v_i_4499_);
v___x_4507_ = lean_ptr_addr(v_fst_4504_);
v___x_4508_ = ((size_t)3ULL);
v___x_4509_ = lean_usize_shift_right(v___x_4507_, v___x_4508_);
v___x_4510_ = lean_usize_to_uint64(v___x_4509_);
v___x_4511_ = lean_ptr_addr(v_snd_4505_);
v___x_4512_ = lean_usize_shift_right(v___x_4511_, v___x_4508_);
v___x_4513_ = lean_usize_to_uint64(v___x_4512_);
v___x_4514_ = lean_uint64_mix_hash(v___x_4510_, v___x_4513_);
v_h_4515_ = lean_uint64_to_usize(v___x_4514_);
v___x_4516_ = ((size_t)5ULL);
v___x_4517_ = lean_unsigned_to_nat(1u);
v___x_4518_ = ((size_t)1ULL);
v___x_4519_ = lean_usize_sub(v_depth_4496_, v___x_4518_);
v___x_4520_ = lean_usize_mul(v___x_4516_, v___x_4519_);
v_h_4521_ = lean_usize_shift_right(v_h_4515_, v___x_4520_);
v___x_4522_ = lean_nat_add(v_i_4499_, v___x_4517_);
lean_dec(v_i_4499_);
lean_inc(v_v_4506_);
lean_inc(v_k_4503_);
v___x_4523_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_entries_4500_, v_h_4521_, v_depth_4496_, v_k_4503_, v_v_4506_);
v_i_4499_ = v___x_4522_;
v_entries_4500_ = v___x_4523_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_4525_, lean_object* v_keys_4526_, lean_object* v_vals_4527_, lean_object* v_i_4528_, lean_object* v_entries_4529_){
_start:
{
size_t v_depth_boxed_4530_; lean_object* v_res_4531_; 
v_depth_boxed_4530_ = lean_unbox_usize(v_depth_4525_);
lean_dec(v_depth_4525_);
v_res_4531_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_boxed_4530_, v_keys_4526_, v_vals_4527_, v_i_4528_, v_entries_4529_);
lean_dec_ref(v_vals_4527_);
lean_dec_ref(v_keys_4526_);
return v_res_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___boxed(lean_object* v_x_4532_, lean_object* v_x_4533_, lean_object* v_x_4534_, lean_object* v_x_4535_, lean_object* v_x_4536_){
_start:
{
size_t v_x_3066__boxed_4537_; size_t v_x_3067__boxed_4538_; lean_object* v_res_4539_; 
v_x_3066__boxed_4537_ = lean_unbox_usize(v_x_4533_);
lean_dec(v_x_4533_);
v_x_3067__boxed_4538_ = lean_unbox_usize(v_x_4534_);
lean_dec(v_x_4534_);
v_res_4539_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4532_, v_x_3066__boxed_4537_, v_x_3067__boxed_4538_, v_x_4535_, v_x_4536_);
return v_res_4539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(lean_object* v_x_4540_, lean_object* v_x_4541_, lean_object* v_x_4542_){
_start:
{
lean_object* v_fst_4543_; lean_object* v_snd_4544_; size_t v___x_4545_; size_t v___x_4546_; size_t v___x_4547_; uint64_t v___x_4548_; size_t v___x_4549_; size_t v___x_4550_; uint64_t v___x_4551_; uint64_t v___x_4552_; size_t v___x_4553_; size_t v___x_4554_; lean_object* v___x_4555_; 
v_fst_4543_ = lean_ctor_get(v_x_4541_, 0);
v_snd_4544_ = lean_ctor_get(v_x_4541_, 1);
v___x_4545_ = lean_ptr_addr(v_fst_4543_);
v___x_4546_ = ((size_t)3ULL);
v___x_4547_ = lean_usize_shift_right(v___x_4545_, v___x_4546_);
v___x_4548_ = lean_usize_to_uint64(v___x_4547_);
v___x_4549_ = lean_ptr_addr(v_snd_4544_);
v___x_4550_ = lean_usize_shift_right(v___x_4549_, v___x_4546_);
v___x_4551_ = lean_usize_to_uint64(v___x_4550_);
v___x_4552_ = lean_uint64_mix_hash(v___x_4548_, v___x_4551_);
v___x_4553_ = lean_uint64_to_usize(v___x_4552_);
v___x_4554_ = ((size_t)1ULL);
v___x_4555_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4540_, v___x_4553_, v___x_4554_, v_x_4541_, v_x_4542_);
return v___x_4555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object* v_s_4556_, lean_object* v_t_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_){
_start:
{
lean_object* v___x_4564_; lean_object* v_defEqI_4565_; lean_object* v_key_4566_; lean_object* v___x_4567_; 
v___x_4564_ = lean_st_ref_get(v_a_4558_);
v_defEqI_4565_ = lean_ctor_get(v___x_4564_, 6);
lean_inc_ref(v_defEqI_4565_);
lean_dec(v___x_4564_);
lean_inc_ref(v_t_4557_);
lean_inc_ref(v_s_4556_);
v_key_4566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_4566_, 0, v_s_4556_);
lean_ctor_set(v_key_4566_, 1, v_t_4557_);
v___x_4567_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_defEqI_4565_, v_key_4566_);
lean_dec_ref(v_defEqI_4565_);
if (lean_obj_tag(v___x_4567_) == 1)
{
lean_object* v_val_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4575_; 
lean_dec_ref_known(v_key_4566_, 2);
lean_dec_ref(v_t_4557_);
lean_dec_ref(v_s_4556_);
v_val_4568_ = lean_ctor_get(v___x_4567_, 0);
v_isSharedCheck_4575_ = !lean_is_exclusive(v___x_4567_);
if (v_isSharedCheck_4575_ == 0)
{
v___x_4570_ = v___x_4567_;
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_val_4568_);
lean_dec(v___x_4567_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
lean_object* v___x_4573_; 
if (v_isShared_4571_ == 0)
{
lean_ctor_set_tag(v___x_4570_, 0);
v___x_4573_ = v___x_4570_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v_val_4568_);
v___x_4573_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
return v___x_4573_;
}
}
}
else
{
lean_object* v___x_4576_; 
lean_dec(v___x_4567_);
v___x_4576_ = l_Lean_Meta_isDefEqI(v_s_4556_, v_t_4557_, v_a_4559_, v_a_4560_, v_a_4561_, v_a_4562_);
if (lean_obj_tag(v___x_4576_) == 0)
{
lean_object* v_a_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4606_; 
v_a_4577_ = lean_ctor_get(v___x_4576_, 0);
v_isSharedCheck_4606_ = !lean_is_exclusive(v___x_4576_);
if (v_isSharedCheck_4606_ == 0)
{
v___x_4579_ = v___x_4576_;
v_isShared_4580_ = v_isSharedCheck_4606_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_a_4577_);
lean_dec(v___x_4576_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4606_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v___x_4581_; lean_object* v_share_4582_; lean_object* v_maxFVar_4583_; lean_object* v_proofInstInfo_4584_; lean_object* v_inferType_4585_; lean_object* v_getLevel_4586_; lean_object* v_congrInfo_4587_; lean_object* v_defEqI_4588_; lean_object* v_extensions_4589_; lean_object* v_issues_4590_; lean_object* v_canon_4591_; lean_object* v_instanceOverrides_4592_; uint8_t v_debug_4593_; lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4605_; 
v___x_4581_ = lean_st_ref_take(v_a_4558_);
v_share_4582_ = lean_ctor_get(v___x_4581_, 0);
v_maxFVar_4583_ = lean_ctor_get(v___x_4581_, 1);
v_proofInstInfo_4584_ = lean_ctor_get(v___x_4581_, 2);
v_inferType_4585_ = lean_ctor_get(v___x_4581_, 3);
v_getLevel_4586_ = lean_ctor_get(v___x_4581_, 4);
v_congrInfo_4587_ = lean_ctor_get(v___x_4581_, 5);
v_defEqI_4588_ = lean_ctor_get(v___x_4581_, 6);
v_extensions_4589_ = lean_ctor_get(v___x_4581_, 7);
v_issues_4590_ = lean_ctor_get(v___x_4581_, 8);
v_canon_4591_ = lean_ctor_get(v___x_4581_, 9);
v_instanceOverrides_4592_ = lean_ctor_get(v___x_4581_, 10);
v_debug_4593_ = lean_ctor_get_uint8(v___x_4581_, sizeof(void*)*11);
v_isSharedCheck_4605_ = !lean_is_exclusive(v___x_4581_);
if (v_isSharedCheck_4605_ == 0)
{
v___x_4595_ = v___x_4581_;
v_isShared_4596_ = v_isSharedCheck_4605_;
goto v_resetjp_4594_;
}
else
{
lean_inc(v_instanceOverrides_4592_);
lean_inc(v_canon_4591_);
lean_inc(v_issues_4590_);
lean_inc(v_extensions_4589_);
lean_inc(v_defEqI_4588_);
lean_inc(v_congrInfo_4587_);
lean_inc(v_getLevel_4586_);
lean_inc(v_inferType_4585_);
lean_inc(v_proofInstInfo_4584_);
lean_inc(v_maxFVar_4583_);
lean_inc(v_share_4582_);
lean_dec(v___x_4581_);
v___x_4595_ = lean_box(0);
v_isShared_4596_ = v_isSharedCheck_4605_;
goto v_resetjp_4594_;
}
v_resetjp_4594_:
{
lean_object* v___x_4597_; lean_object* v___x_4599_; 
lean_inc(v_a_4577_);
v___x_4597_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_defEqI_4588_, v_key_4566_, v_a_4577_);
if (v_isShared_4596_ == 0)
{
lean_ctor_set(v___x_4595_, 6, v___x_4597_);
v___x_4599_ = v___x_4595_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4604_; 
v_reuseFailAlloc_4604_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_4604_, 0, v_share_4582_);
lean_ctor_set(v_reuseFailAlloc_4604_, 1, v_maxFVar_4583_);
lean_ctor_set(v_reuseFailAlloc_4604_, 2, v_proofInstInfo_4584_);
lean_ctor_set(v_reuseFailAlloc_4604_, 3, v_inferType_4585_);
lean_ctor_set(v_reuseFailAlloc_4604_, 4, v_getLevel_4586_);
lean_ctor_set(v_reuseFailAlloc_4604_, 5, v_congrInfo_4587_);
lean_ctor_set(v_reuseFailAlloc_4604_, 6, v___x_4597_);
lean_ctor_set(v_reuseFailAlloc_4604_, 7, v_extensions_4589_);
lean_ctor_set(v_reuseFailAlloc_4604_, 8, v_issues_4590_);
lean_ctor_set(v_reuseFailAlloc_4604_, 9, v_canon_4591_);
lean_ctor_set(v_reuseFailAlloc_4604_, 10, v_instanceOverrides_4592_);
lean_ctor_set_uint8(v_reuseFailAlloc_4604_, sizeof(void*)*11, v_debug_4593_);
v___x_4599_ = v_reuseFailAlloc_4604_;
goto v_reusejp_4598_;
}
v_reusejp_4598_:
{
lean_object* v___x_4600_; lean_object* v___x_4602_; 
v___x_4600_ = lean_st_ref_put(v_a_4558_, v___x_4599_);
if (v_isShared_4580_ == 0)
{
v___x_4602_ = v___x_4579_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v_a_4577_);
v___x_4602_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
return v___x_4602_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_4566_, 2);
return v___x_4576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg___boxed(lean_object* v_s_4607_, lean_object* v_t_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_){
_start:
{
lean_object* v_res_4615_; 
v_res_4615_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_4607_, v_t_4608_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_);
lean_dec(v_a_4613_);
lean_dec_ref(v_a_4612_);
lean_dec(v_a_4611_);
lean_dec_ref(v_a_4610_);
lean_dec(v_a_4609_);
return v_res_4615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI(lean_object* v_s_4616_, lean_object* v_t_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_){
_start:
{
lean_object* v___x_4625_; 
v___x_4625_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_4616_, v_t_4617_, v_a_4619_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_);
return v___x_4625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___boxed(lean_object* v_s_4626_, lean_object* v_t_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_){
_start:
{
lean_object* v_res_4635_; 
v_res_4635_ = l_Lean_Meta_Sym_isDefEqI(v_s_4626_, v_t_4627_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_);
lean_dec(v_a_4633_);
lean_dec_ref(v_a_4632_);
lean_dec(v_a_4631_);
lean_dec_ref(v_a_4630_);
lean_dec(v_a_4629_);
lean_dec_ref(v_a_4628_);
return v_res_4635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(lean_object* v_00_u03b2_4636_, lean_object* v_x_4637_, lean_object* v_x_4638_){
_start:
{
lean_object* v___x_4639_; 
v___x_4639_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_4637_, v_x_4638_);
return v___x_4639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___boxed(lean_object* v_00_u03b2_4640_, lean_object* v_x_4641_, lean_object* v_x_4642_){
_start:
{
lean_object* v_res_4643_; 
v_res_4643_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(v_00_u03b2_4640_, v_x_4641_, v_x_4642_);
lean_dec_ref(v_x_4642_);
lean_dec_ref(v_x_4641_);
return v_res_4643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1(lean_object* v_00_u03b2_4644_, lean_object* v_x_4645_, lean_object* v_x_4646_, lean_object* v_x_4647_){
_start:
{
lean_object* v___x_4648_; 
v___x_4648_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_x_4645_, v_x_4646_, v_x_4647_);
return v___x_4648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(lean_object* v_00_u03b2_4649_, lean_object* v_x_4650_, size_t v_x_4651_, lean_object* v_x_4652_){
_start:
{
lean_object* v___x_4653_; 
v___x_4653_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4650_, v_x_4651_, v_x_4652_);
return v___x_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4654_, lean_object* v_x_4655_, lean_object* v_x_4656_, lean_object* v_x_4657_){
_start:
{
size_t v_x_3362__boxed_4658_; lean_object* v_res_4659_; 
v_x_3362__boxed_4658_ = lean_unbox_usize(v_x_4656_);
lean_dec(v_x_4656_);
v_res_4659_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(v_00_u03b2_4654_, v_x_4655_, v_x_3362__boxed_4658_, v_x_4657_);
lean_dec_ref(v_x_4657_);
lean_dec_ref(v_x_4655_);
return v_res_4659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(lean_object* v_00_u03b2_4660_, lean_object* v_x_4661_, size_t v_x_4662_, size_t v_x_4663_, lean_object* v_x_4664_, lean_object* v_x_4665_){
_start:
{
lean_object* v___x_4666_; 
v___x_4666_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4661_, v_x_4662_, v_x_4663_, v_x_4664_, v_x_4665_);
return v___x_4666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4667_, lean_object* v_x_4668_, lean_object* v_x_4669_, lean_object* v_x_4670_, lean_object* v_x_4671_, lean_object* v_x_4672_){
_start:
{
size_t v_x_3373__boxed_4673_; size_t v_x_3374__boxed_4674_; lean_object* v_res_4675_; 
v_x_3373__boxed_4673_ = lean_unbox_usize(v_x_4669_);
lean_dec(v_x_4669_);
v_x_3374__boxed_4674_ = lean_unbox_usize(v_x_4670_);
lean_dec(v_x_4670_);
v_res_4675_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(v_00_u03b2_4667_, v_x_4668_, v_x_3373__boxed_4673_, v_x_3374__boxed_4674_, v_x_4671_, v_x_4672_);
return v_res_4675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4676_, lean_object* v_keys_4677_, lean_object* v_vals_4678_, lean_object* v_heq_4679_, lean_object* v_i_4680_, lean_object* v_k_4681_){
_start:
{
lean_object* v___x_4682_; 
v___x_4682_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_4677_, v_vals_4678_, v_i_4680_, v_k_4681_);
return v___x_4682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4683_, lean_object* v_keys_4684_, lean_object* v_vals_4685_, lean_object* v_heq_4686_, lean_object* v_i_4687_, lean_object* v_k_4688_){
_start:
{
lean_object* v_res_4689_; 
v_res_4689_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(v_00_u03b2_4683_, v_keys_4684_, v_vals_4685_, v_heq_4686_, v_i_4687_, v_k_4688_);
lean_dec_ref(v_k_4688_);
lean_dec_ref(v_vals_4685_);
lean_dec_ref(v_keys_4684_);
return v_res_4689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4690_, lean_object* v_n_4691_, lean_object* v_k_4692_, lean_object* v_v_4693_){
_start:
{
lean_object* v___x_4694_; 
v___x_4694_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v_n_4691_, v_k_4692_, v_v_4693_);
return v___x_4694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_4695_, size_t v_depth_4696_, lean_object* v_keys_4697_, lean_object* v_vals_4698_, lean_object* v_heq_4699_, lean_object* v_i_4700_, lean_object* v_entries_4701_){
_start:
{
lean_object* v___x_4702_; 
v___x_4702_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_4696_, v_keys_4697_, v_vals_4698_, v_i_4700_, v_entries_4701_);
return v___x_4702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_4703_, lean_object* v_depth_4704_, lean_object* v_keys_4705_, lean_object* v_vals_4706_, lean_object* v_heq_4707_, lean_object* v_i_4708_, lean_object* v_entries_4709_){
_start:
{
size_t v_depth_boxed_4710_; lean_object* v_res_4711_; 
v_depth_boxed_4710_ = lean_unbox_usize(v_depth_4704_);
lean_dec(v_depth_4704_);
v_res_4711_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(v_00_u03b2_4703_, v_depth_boxed_4710_, v_keys_4705_, v_vals_4706_, v_heq_4707_, v_i_4708_, v_entries_4709_);
lean_dec_ref(v_vals_4706_);
lean_dec_ref(v_keys_4705_);
return v_res_4711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_4712_, lean_object* v_x_4713_, lean_object* v_x_4714_, lean_object* v_x_4715_, lean_object* v_x_4716_){
_start:
{
lean_object* v___x_4717_; 
v___x_4717_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_x_4713_, v_x_4714_, v_x_4715_, v_x_4716_);
return v___x_4717_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0(void){
_start:
{
lean_object* v___x_4718_; lean_object* v___f_4719_; 
v___x_4718_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_4719_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4719_, 0, v___x_4718_);
return v___f_4719_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__1(void){
_start:
{
lean_object* v___x_4720_; lean_object* v___f_4721_; 
v___x_4720_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_4721_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4721_, 0, v___x_4720_);
return v___f_4721_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__2(void){
_start:
{
lean_object* v___f_4722_; lean_object* v___f_4723_; lean_object* v___x_4724_; 
v___f_4722_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__1, &l_Lean_Meta_Sym_instInhabitedSymM___closed__1_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__1);
v___f_4723_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__0, &l_Lean_Meta_Sym_instInhabitedSymM___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0);
v___x_4724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4724_, 0, v___f_4723_);
lean_ctor_set(v___x_4724_, 1, v___f_4722_);
return v___x_4724_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__3(void){
_start:
{
lean_object* v___x_4725_; lean_object* v___f_4726_; 
v___x_4725_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__2, &l_Lean_Meta_Sym_instInhabitedSymM___closed__2_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__2);
v___f_4726_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4726_, 0, v___x_4725_);
return v___f_4726_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__4(void){
_start:
{
lean_object* v___x_4727_; lean_object* v___f_4728_; 
v___x_4727_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__2, &l_Lean_Meta_Sym_instInhabitedSymM___closed__2_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__2);
v___f_4728_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4728_, 0, v___x_4727_);
return v___f_4728_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__5(void){
_start:
{
lean_object* v___f_4729_; lean_object* v___f_4730_; lean_object* v___x_4731_; 
v___f_4729_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__4, &l_Lean_Meta_Sym_instInhabitedSymM___closed__4_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__4);
v___f_4730_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__3, &l_Lean_Meta_Sym_instInhabitedSymM___closed__3_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__3);
v___x_4731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4731_, 0, v___f_4730_);
lean_ctor_set(v___x_4731_, 1, v___f_4729_);
return v___x_4731_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__6(void){
_start:
{
lean_object* v___x_4732_; lean_object* v___f_4733_; 
v___x_4732_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__5, &l_Lean_Meta_Sym_instInhabitedSymM___closed__5_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__5);
v___f_4733_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4733_, 0, v___x_4732_);
return v___f_4733_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__7(void){
_start:
{
lean_object* v___x_4734_; lean_object* v___f_4735_; 
v___x_4734_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__5, &l_Lean_Meta_Sym_instInhabitedSymM___closed__5_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__5);
v___f_4735_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4735_, 0, v___x_4734_);
return v___f_4735_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8(void){
_start:
{
lean_object* v___f_4736_; lean_object* v___f_4737_; lean_object* v___x_4738_; 
v___f_4736_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__7, &l_Lean_Meta_Sym_instInhabitedSymM___closed__7_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__7);
v___f_4737_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__6, &l_Lean_Meta_Sym_instInhabitedSymM___closed__6_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__6);
v___x_4738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4738_, 0, v___f_4737_);
lean_ctor_set(v___x_4738_, 1, v___f_4736_);
return v___x_4738_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__9(void){
_start:
{
lean_object* v___x_4739_; lean_object* v___f_4740_; 
v___x_4739_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__8, &l_Lean_Meta_Sym_instInhabitedSymM___closed__8_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8);
v___f_4740_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4740_, 0, v___x_4739_);
return v___f_4740_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__10(void){
_start:
{
lean_object* v___x_4741_; lean_object* v___f_4742_; 
v___x_4741_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__8, &l_Lean_Meta_Sym_instInhabitedSymM___closed__8_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8);
v___f_4742_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4742_, 0, v___x_4741_);
return v___f_4742_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__11(void){
_start:
{
lean_object* v___f_4743_; lean_object* v___f_4744_; lean_object* v___x_4745_; 
v___f_4743_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__10, &l_Lean_Meta_Sym_instInhabitedSymM___closed__10_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__10);
v___f_4744_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__9, &l_Lean_Meta_Sym_instInhabitedSymM___closed__9_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__9);
v___x_4745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4745_, 0, v___f_4744_);
lean_ctor_set(v___x_4745_, 1, v___f_4743_);
return v___x_4745_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__16(void){
_start:
{
lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; 
v___x_4750_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_4751_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__15));
v___x_4752_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__14));
v___x_4753_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_4752_, v___x_4751_, v___x_4750_);
return v___x_4753_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__17(void){
_start:
{
lean_object* v___x_4754_; lean_object* v___f_4755_; lean_object* v___f_4756_; lean_object* v___x_4757_; 
v___x_4754_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__16, &l_Lean_Meta_Sym_instInhabitedSymM___closed__16_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__16);
v___f_4755_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__13));
v___f_4756_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__12));
v___x_4757_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_4756_, v___f_4755_, v___x_4754_);
return v___x_4757_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__18(void){
_start:
{
lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; 
v___x_4758_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__17, &l_Lean_Meta_Sym_instInhabitedSymM___closed__17_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__17);
v___x_4759_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__15));
v___x_4760_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__14));
v___x_4761_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_4760_, v___x_4759_, v___x_4758_);
return v___x_4761_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__19(void){
_start:
{
lean_object* v___x_4762_; lean_object* v___f_4763_; lean_object* v___f_4764_; lean_object* v___x_4765_; 
v___x_4762_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__18, &l_Lean_Meta_Sym_instInhabitedSymM___closed__18_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__18);
v___f_4763_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__13));
v___f_4764_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__12));
v___x_4765_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_4764_, v___f_4763_, v___x_4762_);
return v___x_4765_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__20(void){
_start:
{
lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___f_4768_; 
v___x_4766_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__15));
v___x_4767_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_4768_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4768_, 0, v___x_4767_);
lean_closure_set(v___f_4768_, 1, v___x_4766_);
return v___f_4768_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__21(void){
_start:
{
lean_object* v___f_4769_; lean_object* v___f_4770_; lean_object* v___f_4771_; 
v___f_4769_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__13));
v___f_4770_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__20, &l_Lean_Meta_Sym_instInhabitedSymM___closed__20_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__20);
v___f_4771_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4771_, 0, v___f_4770_);
lean_closure_set(v___f_4771_, 1, v___f_4769_);
return v___f_4771_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__23(void){
_start:
{
lean_object* v___x_4773_; lean_object* v___x_4774_; 
v___x_4773_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__22));
v___x_4774_ = l_Lean_stringToMessageData(v___x_4773_);
return v___x_4774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object* v_00_u03b1_4775_){
_start:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v_toApplicative_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4845_; 
v___x_4776_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0);
v___x_4777_ = l_StateRefT_x27_instMonad___redArg(v___x_4776_);
v_toApplicative_4778_ = lean_ctor_get(v___x_4777_, 0);
v_isSharedCheck_4845_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4845_ == 0)
{
lean_object* v_unused_4846_; 
v_unused_4846_ = lean_ctor_get(v___x_4777_, 1);
lean_dec(v_unused_4846_);
v___x_4780_ = v___x_4777_;
v_isShared_4781_ = v_isSharedCheck_4845_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_toApplicative_4778_);
lean_dec(v___x_4777_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4845_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v_toFunctor_4782_; lean_object* v_toSeq_4783_; lean_object* v_toSeqLeft_4784_; lean_object* v_toSeqRight_4785_; lean_object* v___x_4787_; uint8_t v_isShared_4788_; uint8_t v_isSharedCheck_4843_; 
v_toFunctor_4782_ = lean_ctor_get(v_toApplicative_4778_, 0);
v_toSeq_4783_ = lean_ctor_get(v_toApplicative_4778_, 2);
v_toSeqLeft_4784_ = lean_ctor_get(v_toApplicative_4778_, 3);
v_toSeqRight_4785_ = lean_ctor_get(v_toApplicative_4778_, 4);
v_isSharedCheck_4843_ = !lean_is_exclusive(v_toApplicative_4778_);
if (v_isSharedCheck_4843_ == 0)
{
lean_object* v_unused_4844_; 
v_unused_4844_ = lean_ctor_get(v_toApplicative_4778_, 1);
lean_dec(v_unused_4844_);
v___x_4787_ = v_toApplicative_4778_;
v_isShared_4788_ = v_isSharedCheck_4843_;
goto v_resetjp_4786_;
}
else
{
lean_inc(v_toSeqRight_4785_);
lean_inc(v_toSeqLeft_4784_);
lean_inc(v_toSeq_4783_);
lean_inc(v_toFunctor_4782_);
lean_dec(v_toApplicative_4778_);
v___x_4787_ = lean_box(0);
v_isShared_4788_ = v_isSharedCheck_4843_;
goto v_resetjp_4786_;
}
v_resetjp_4786_:
{
lean_object* v___f_4789_; lean_object* v___f_4790_; lean_object* v___f_4791_; lean_object* v___f_4792_; lean_object* v___x_4793_; lean_object* v___f_4794_; lean_object* v___f_4795_; lean_object* v___f_4796_; lean_object* v___x_4798_; 
v___f_4789_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1));
v___f_4790_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4782_);
v___f_4791_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4791_, 0, v_toFunctor_4782_);
v___f_4792_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4792_, 0, v_toFunctor_4782_);
v___x_4793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4793_, 0, v___f_4791_);
lean_ctor_set(v___x_4793_, 1, v___f_4792_);
v___f_4794_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4794_, 0, v_toSeqRight_4785_);
v___f_4795_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4795_, 0, v_toSeqLeft_4784_);
v___f_4796_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4796_, 0, v_toSeq_4783_);
if (v_isShared_4788_ == 0)
{
lean_ctor_set(v___x_4787_, 4, v___f_4794_);
lean_ctor_set(v___x_4787_, 3, v___f_4795_);
lean_ctor_set(v___x_4787_, 2, v___f_4796_);
lean_ctor_set(v___x_4787_, 1, v___f_4789_);
lean_ctor_set(v___x_4787_, 0, v___x_4793_);
v___x_4798_ = v___x_4787_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4842_; 
v_reuseFailAlloc_4842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4842_, 0, v___x_4793_);
lean_ctor_set(v_reuseFailAlloc_4842_, 1, v___f_4789_);
lean_ctor_set(v_reuseFailAlloc_4842_, 2, v___f_4796_);
lean_ctor_set(v_reuseFailAlloc_4842_, 3, v___f_4795_);
lean_ctor_set(v_reuseFailAlloc_4842_, 4, v___f_4794_);
v___x_4798_ = v_reuseFailAlloc_4842_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
lean_object* v___x_4800_; 
if (v_isShared_4781_ == 0)
{
lean_ctor_set(v___x_4780_, 1, v___f_4790_);
lean_ctor_set(v___x_4780_, 0, v___x_4798_);
v___x_4800_ = v___x_4780_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v___x_4798_);
lean_ctor_set(v_reuseFailAlloc_4841_, 1, v___f_4790_);
v___x_4800_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
lean_object* v___x_4801_; lean_object* v_toApplicative_4802_; lean_object* v___x_4804_; uint8_t v_isShared_4805_; uint8_t v_isSharedCheck_4839_; 
v___x_4801_ = l_StateRefT_x27_instMonad___redArg(v___x_4800_);
v_toApplicative_4802_ = lean_ctor_get(v___x_4801_, 0);
v_isSharedCheck_4839_ = !lean_is_exclusive(v___x_4801_);
if (v_isSharedCheck_4839_ == 0)
{
lean_object* v_unused_4840_; 
v_unused_4840_ = lean_ctor_get(v___x_4801_, 1);
lean_dec(v_unused_4840_);
v___x_4804_ = v___x_4801_;
v_isShared_4805_ = v_isSharedCheck_4839_;
goto v_resetjp_4803_;
}
else
{
lean_inc(v_toApplicative_4802_);
lean_dec(v___x_4801_);
v___x_4804_ = lean_box(0);
v_isShared_4805_ = v_isSharedCheck_4839_;
goto v_resetjp_4803_;
}
v_resetjp_4803_:
{
lean_object* v_toFunctor_4806_; lean_object* v_toSeq_4807_; lean_object* v_toSeqLeft_4808_; lean_object* v_toSeqRight_4809_; lean_object* v___x_4811_; uint8_t v_isShared_4812_; uint8_t v_isSharedCheck_4837_; 
v_toFunctor_4806_ = lean_ctor_get(v_toApplicative_4802_, 0);
v_toSeq_4807_ = lean_ctor_get(v_toApplicative_4802_, 2);
v_toSeqLeft_4808_ = lean_ctor_get(v_toApplicative_4802_, 3);
v_toSeqRight_4809_ = lean_ctor_get(v_toApplicative_4802_, 4);
v_isSharedCheck_4837_ = !lean_is_exclusive(v_toApplicative_4802_);
if (v_isSharedCheck_4837_ == 0)
{
lean_object* v_unused_4838_; 
v_unused_4838_ = lean_ctor_get(v_toApplicative_4802_, 1);
lean_dec(v_unused_4838_);
v___x_4811_ = v_toApplicative_4802_;
v_isShared_4812_ = v_isSharedCheck_4837_;
goto v_resetjp_4810_;
}
else
{
lean_inc(v_toSeqRight_4809_);
lean_inc(v_toSeqLeft_4808_);
lean_inc(v_toSeq_4807_);
lean_inc(v_toFunctor_4806_);
lean_dec(v_toApplicative_4802_);
v___x_4811_ = lean_box(0);
v_isShared_4812_ = v_isSharedCheck_4837_;
goto v_resetjp_4810_;
}
v_resetjp_4810_:
{
lean_object* v___f_4813_; lean_object* v___f_4814_; lean_object* v___f_4815_; lean_object* v___f_4816_; lean_object* v___x_4817_; lean_object* v___f_4818_; lean_object* v___f_4819_; lean_object* v___f_4820_; lean_object* v___x_4822_; 
v___f_4813_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3));
v___f_4814_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4806_);
v___f_4815_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4815_, 0, v_toFunctor_4806_);
v___f_4816_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4816_, 0, v_toFunctor_4806_);
v___x_4817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4817_, 0, v___f_4815_);
lean_ctor_set(v___x_4817_, 1, v___f_4816_);
v___f_4818_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4818_, 0, v_toSeqRight_4809_);
v___f_4819_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4819_, 0, v_toSeqLeft_4808_);
v___f_4820_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4820_, 0, v_toSeq_4807_);
if (v_isShared_4812_ == 0)
{
lean_ctor_set(v___x_4811_, 4, v___f_4818_);
lean_ctor_set(v___x_4811_, 3, v___f_4819_);
lean_ctor_set(v___x_4811_, 2, v___f_4820_);
lean_ctor_set(v___x_4811_, 1, v___f_4813_);
lean_ctor_set(v___x_4811_, 0, v___x_4817_);
v___x_4822_ = v___x_4811_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4836_; 
v_reuseFailAlloc_4836_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4836_, 0, v___x_4817_);
lean_ctor_set(v_reuseFailAlloc_4836_, 1, v___f_4813_);
lean_ctor_set(v_reuseFailAlloc_4836_, 2, v___f_4820_);
lean_ctor_set(v_reuseFailAlloc_4836_, 3, v___f_4819_);
lean_ctor_set(v_reuseFailAlloc_4836_, 4, v___f_4818_);
v___x_4822_ = v_reuseFailAlloc_4836_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
lean_object* v___x_4824_; 
if (v_isShared_4805_ == 0)
{
lean_ctor_set(v___x_4804_, 1, v___f_4814_);
lean_ctor_set(v___x_4804_, 0, v___x_4822_);
v___x_4824_ = v___x_4804_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v___x_4822_);
lean_ctor_set(v_reuseFailAlloc_4835_, 1, v___f_4814_);
v___x_4824_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v_toMonadRef_4829_; lean_object* v___f_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; 
v___x_4825_ = l_StateRefT_x27_instMonad___redArg(v___x_4824_);
v___x_4826_ = l_ReaderT_instMonad___redArg(v___x_4825_);
v___x_4827_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__11, &l_Lean_Meta_Sym_instInhabitedSymM___closed__11_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__11);
v___x_4828_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__19, &l_Lean_Meta_Sym_instInhabitedSymM___closed__19_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__19);
v_toMonadRef_4829_ = lean_ctor_get(v___x_4828_, 0);
v___f_4830_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__21, &l_Lean_Meta_Sym_instInhabitedSymM___closed__21_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__21);
lean_inc_ref(v___x_4826_);
v___x_4831_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_4830_, v___x_4826_);
lean_inc_ref(v_toMonadRef_4829_);
v___x_4832_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4832_, 0, v___x_4827_);
lean_ctor_set(v___x_4832_, 1, v_toMonadRef_4829_);
lean_ctor_set(v___x_4832_, 2, v___x_4831_);
v___x_4833_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__23, &l_Lean_Meta_Sym_instInhabitedSymM___closed__23_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__23);
v___x_4834_ = l_Lean_throwError___redArg(v___x_4826_, v___x_4832_, v___x_4833_);
return v___x_4834_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(lean_object* v_ext_4847_, lean_object* v_extensions_4848_){
_start:
{
lean_object* v_id_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; 
v_id_4850_ = lean_ctor_get(v_ext_4847_, 0);
v___x_4851_ = l_Lean_Meta_Sym_instInhabitedSymExtensionState;
v___x_4852_ = lean_array_get_borrowed(v___x_4851_, v_extensions_4848_, v_id_4850_);
lean_inc(v___x_4852_);
v___x_4853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4853_, 0, v___x_4852_);
return v___x_4853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg___boxed(lean_object* v_ext_4854_, lean_object* v_extensions_4855_, lean_object* v_a_4856_){
_start:
{
lean_object* v_res_4857_; 
v_res_4857_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_4854_, v_extensions_4855_);
lean_dec_ref(v_extensions_4855_);
lean_dec_ref(v_ext_4854_);
return v_res_4857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(lean_object* v_00_u03c3_4858_, lean_object* v_ext_4859_, lean_object* v_extensions_4860_){
_start:
{
lean_object* v___x_4862_; 
v___x_4862_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_4859_, v_extensions_4860_);
return v___x_4862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___boxed(lean_object* v_00_u03c3_4863_, lean_object* v_ext_4864_, lean_object* v_extensions_4865_, lean_object* v_a_4866_){
_start:
{
lean_object* v_res_4867_; 
v_res_4867_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(v_00_u03c3_4863_, v_ext_4864_, v_extensions_4865_);
lean_dec_ref(v_extensions_4865_);
lean_dec_ref(v_ext_4864_);
return v_res_4867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg(lean_object* v_ext_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_){
_start:
{
lean_object* v___x_4872_; lean_object* v_extensions_4873_; lean_object* v___x_4874_; 
v___x_4872_ = lean_st_ref_get(v_a_4869_);
v_extensions_4873_ = lean_ctor_get(v___x_4872_, 7);
lean_inc_ref(v_extensions_4873_);
lean_dec(v___x_4872_);
v___x_4874_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_4868_, v_extensions_4873_);
lean_dec_ref(v_extensions_4873_);
if (lean_obj_tag(v___x_4874_) == 0)
{
lean_object* v_a_4875_; lean_object* v___x_4877_; uint8_t v_isShared_4878_; uint8_t v_isSharedCheck_4882_; 
v_a_4875_ = lean_ctor_get(v___x_4874_, 0);
v_isSharedCheck_4882_ = !lean_is_exclusive(v___x_4874_);
if (v_isSharedCheck_4882_ == 0)
{
v___x_4877_ = v___x_4874_;
v_isShared_4878_ = v_isSharedCheck_4882_;
goto v_resetjp_4876_;
}
else
{
lean_inc(v_a_4875_);
lean_dec(v___x_4874_);
v___x_4877_ = lean_box(0);
v_isShared_4878_ = v_isSharedCheck_4882_;
goto v_resetjp_4876_;
}
v_resetjp_4876_:
{
lean_object* v___x_4880_; 
if (v_isShared_4878_ == 0)
{
v___x_4880_ = v___x_4877_;
goto v_reusejp_4879_;
}
else
{
lean_object* v_reuseFailAlloc_4881_; 
v_reuseFailAlloc_4881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4881_, 0, v_a_4875_);
v___x_4880_ = v_reuseFailAlloc_4881_;
goto v_reusejp_4879_;
}
v_reusejp_4879_:
{
return v___x_4880_;
}
}
}
else
{
lean_object* v_a_4883_; lean_object* v___x_4885_; uint8_t v_isShared_4886_; uint8_t v_isSharedCheck_4895_; 
v_a_4883_ = lean_ctor_get(v___x_4874_, 0);
v_isSharedCheck_4895_ = !lean_is_exclusive(v___x_4874_);
if (v_isSharedCheck_4895_ == 0)
{
v___x_4885_ = v___x_4874_;
v_isShared_4886_ = v_isSharedCheck_4895_;
goto v_resetjp_4884_;
}
else
{
lean_inc(v_a_4883_);
lean_dec(v___x_4874_);
v___x_4885_ = lean_box(0);
v_isShared_4886_ = v_isSharedCheck_4895_;
goto v_resetjp_4884_;
}
v_resetjp_4884_:
{
lean_object* v_ref_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4893_; 
v_ref_4887_ = lean_ctor_get(v_a_4870_, 4);
v___x_4888_ = lean_io_error_to_string(v_a_4883_);
v___x_4889_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4889_, 0, v___x_4888_);
v___x_4890_ = l_Lean_MessageData_ofFormat(v___x_4889_);
lean_inc(v_ref_4887_);
v___x_4891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4891_, 0, v_ref_4887_);
lean_ctor_set(v___x_4891_, 1, v___x_4890_);
if (v_isShared_4886_ == 0)
{
lean_ctor_set(v___x_4885_, 0, v___x_4891_);
v___x_4893_ = v___x_4885_;
goto v_reusejp_4892_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v___x_4891_);
v___x_4893_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4892_;
}
v_reusejp_4892_:
{
return v___x_4893_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg___boxed(lean_object* v_ext_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_){
_start:
{
lean_object* v_res_4900_; 
v_res_4900_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_4896_, v_a_4897_, v_a_4898_);
lean_dec_ref(v_a_4898_);
lean_dec(v_a_4897_);
lean_dec_ref(v_ext_4896_);
return v_res_4900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState(lean_object* v_00_u03c3_4901_, lean_object* v_ext_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_){
_start:
{
lean_object* v___x_4910_; 
v___x_4910_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_4902_, v_a_4904_, v_a_4907_);
return v___x_4910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___boxed(lean_object* v_00_u03c3_4911_, lean_object* v_ext_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_){
_start:
{
lean_object* v_res_4920_; 
v_res_4920_ = l_Lean_Meta_Sym_SymExtension_getState(v_00_u03c3_4911_, v_ext_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_);
lean_dec(v_a_4918_);
lean_dec_ref(v_a_4917_);
lean_dec(v_a_4916_);
lean_dec_ref(v_a_4915_);
lean_dec(v_a_4914_);
lean_dec_ref(v_a_4913_);
lean_dec_ref(v_ext_4912_);
return v_res_4920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(lean_object* v_ext_4921_, lean_object* v_f_4922_, lean_object* v_a_4923_){
_start:
{
lean_object* v___x_4925_; lean_object* v_share_4926_; lean_object* v_maxFVar_4927_; lean_object* v_proofInstInfo_4928_; lean_object* v_inferType_4929_; lean_object* v_getLevel_4930_; lean_object* v_congrInfo_4931_; lean_object* v_defEqI_4932_; lean_object* v_extensions_4933_; lean_object* v_issues_4934_; lean_object* v_canon_4935_; lean_object* v_instanceOverrides_4936_; uint8_t v_debug_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4956_; 
v___x_4925_ = lean_st_ref_take(v_a_4923_);
v_share_4926_ = lean_ctor_get(v___x_4925_, 0);
v_maxFVar_4927_ = lean_ctor_get(v___x_4925_, 1);
v_proofInstInfo_4928_ = lean_ctor_get(v___x_4925_, 2);
v_inferType_4929_ = lean_ctor_get(v___x_4925_, 3);
v_getLevel_4930_ = lean_ctor_get(v___x_4925_, 4);
v_congrInfo_4931_ = lean_ctor_get(v___x_4925_, 5);
v_defEqI_4932_ = lean_ctor_get(v___x_4925_, 6);
v_extensions_4933_ = lean_ctor_get(v___x_4925_, 7);
v_issues_4934_ = lean_ctor_get(v___x_4925_, 8);
v_canon_4935_ = lean_ctor_get(v___x_4925_, 9);
v_instanceOverrides_4936_ = lean_ctor_get(v___x_4925_, 10);
v_debug_4937_ = lean_ctor_get_uint8(v___x_4925_, sizeof(void*)*11);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4925_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4939_ = v___x_4925_;
v_isShared_4940_ = v_isSharedCheck_4956_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_instanceOverrides_4936_);
lean_inc(v_canon_4935_);
lean_inc(v_issues_4934_);
lean_inc(v_extensions_4933_);
lean_inc(v_defEqI_4932_);
lean_inc(v_congrInfo_4931_);
lean_inc(v_getLevel_4930_);
lean_inc(v_inferType_4929_);
lean_inc(v_proofInstInfo_4928_);
lean_inc(v_maxFVar_4927_);
lean_inc(v_share_4926_);
lean_dec(v___x_4925_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_4956_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
lean_object* v_id_4941_; lean_object* v___x_4942_; lean_object* v___y_4944_; lean_object* v___x_4950_; uint8_t v___x_4951_; 
v_id_4941_ = lean_ctor_get(v_ext_4921_, 0);
v___x_4942_ = lean_box(0);
v___x_4950_ = lean_array_get_size(v_extensions_4933_);
v___x_4951_ = lean_nat_dec_lt(v_id_4941_, v___x_4950_);
if (v___x_4951_ == 0)
{
lean_dec(v_f_4922_);
v___y_4944_ = v_extensions_4933_;
goto v___jp_4943_;
}
else
{
lean_object* v_v_4952_; lean_object* v_xs_x27_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; 
v_v_4952_ = lean_array_fget(v_extensions_4933_, v_id_4941_);
v_xs_x27_4953_ = lean_array_fset(v_extensions_4933_, v_id_4941_, v___x_4942_);
v___x_4954_ = lean_apply_1(v_f_4922_, v_v_4952_);
v___x_4955_ = lean_array_fset(v_xs_x27_4953_, v_id_4941_, v___x_4954_);
v___y_4944_ = v___x_4955_;
goto v___jp_4943_;
}
v___jp_4943_:
{
lean_object* v___x_4946_; 
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 7, v___y_4944_);
v___x_4946_ = v___x_4939_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4949_; 
v_reuseFailAlloc_4949_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_4949_, 0, v_share_4926_);
lean_ctor_set(v_reuseFailAlloc_4949_, 1, v_maxFVar_4927_);
lean_ctor_set(v_reuseFailAlloc_4949_, 2, v_proofInstInfo_4928_);
lean_ctor_set(v_reuseFailAlloc_4949_, 3, v_inferType_4929_);
lean_ctor_set(v_reuseFailAlloc_4949_, 4, v_getLevel_4930_);
lean_ctor_set(v_reuseFailAlloc_4949_, 5, v_congrInfo_4931_);
lean_ctor_set(v_reuseFailAlloc_4949_, 6, v_defEqI_4932_);
lean_ctor_set(v_reuseFailAlloc_4949_, 7, v___y_4944_);
lean_ctor_set(v_reuseFailAlloc_4949_, 8, v_issues_4934_);
lean_ctor_set(v_reuseFailAlloc_4949_, 9, v_canon_4935_);
lean_ctor_set(v_reuseFailAlloc_4949_, 10, v_instanceOverrides_4936_);
lean_ctor_set_uint8(v_reuseFailAlloc_4949_, sizeof(void*)*11, v_debug_4937_);
v___x_4946_ = v_reuseFailAlloc_4949_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
lean_object* v___x_4947_; lean_object* v___x_4948_; 
v___x_4947_ = lean_st_ref_put(v_a_4923_, v___x_4946_);
v___x_4948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4948_, 0, v___x_4942_);
return v___x_4948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg___boxed(lean_object* v_ext_4957_, lean_object* v_f_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_){
_start:
{
lean_object* v_res_4961_; 
v_res_4961_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_4957_, v_f_4958_, v_a_4959_);
lean_dec(v_a_4959_);
lean_dec_ref(v_ext_4957_);
return v_res_4961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(lean_object* v_00_u03c3_4962_, lean_object* v_ext_4963_, lean_object* v_f_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_){
_start:
{
lean_object* v___x_4972_; 
v___x_4972_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_4963_, v_f_4964_, v_a_4966_);
return v___x_4972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___boxed(lean_object* v_00_u03c3_4973_, lean_object* v_ext_4974_, lean_object* v_f_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_){
_start:
{
lean_object* v_res_4983_; 
v_res_4983_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(v_00_u03c3_4973_, v_ext_4974_, v_f_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
lean_dec(v_a_4981_);
lean_dec_ref(v_a_4980_);
lean_dec(v_a_4979_);
lean_dec_ref(v_a_4978_);
lean_dec(v_a_4977_);
lean_dec_ref(v_a_4976_);
lean_dec_ref(v_ext_4974_);
return v_res_4983_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareCommon(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CongrTheorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
