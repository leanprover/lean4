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
lean_object* lean_array_uget(lean_object*, size_t);
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_mkProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Sym_isUnfoldReducibleCandidate(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_initializing();
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
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
static const lean_string_object l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0();
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_unfoldReducible___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_unfoldReducible___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_unfoldReducible___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_unfoldReducible___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_unfoldReducible___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_unfoldReducibleStep___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_unfoldReducible___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_unfoldReducible___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1(lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_SymM_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__1;
static const lean_string_object l_Lean_Meta_Sym_SymM_run___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Meta.Sym.SymM"};
static const lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_SymM_run___redArg___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_SymM_run___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Sym.SymM.run"};
static const lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_SymM_run___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_SymM_run___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_SymM_run___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Sym_SymM_run___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__5;
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
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__3;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__4;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__6;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__7;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__9;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__10;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__11;
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__12_value;
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__13_value;
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__14_value;
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__15_value;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__16;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__17;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__18;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__19;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__20;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__21;
static const lean_string_object l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "<SymM default value>"};
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__22 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__22_value;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__23;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0(){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0___closed__1));
v___x_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0___boxed(lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0();
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg(){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___closed__1));
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___boxed(lean_object* v___dummy_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg();
return v_res_155_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0(void){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg();
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default(lean_object* v_00_u03c3_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0, &l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension___redArg(){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0, &l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension___redArg___boxed(lean_object* v___dummy_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_Meta_Sym_instInhabitedSymExtension___redArg();
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension(lean_object* v_a_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0, &l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_));
v___x_169_ = lean_st_mk_ref(v___x_168_);
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2____boxed(lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_();
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg(lean_object* v_ext_173_){
_start:
{
lean_inc_ref(v_ext_173_);
return v_ext_173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg___boxed(lean_object* v_ext_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg(v_ext_174_);
lean_dec_ref(v_ext_174_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1(lean_object* v_00_u03c3_176_, lean_object* v_ext_177_){
_start:
{
lean_inc_ref(v_ext_177_);
return v_ext_177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___boxed(lean_object* v_00_u03c3_178_, lean_object* v_ext_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1(v_00_u03c3_178_, v_ext_179_);
lean_dec_ref(v_ext_179_);
return v_res_180_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = ((lean_object*)(l_Lean_Meta_Sym_registerSymExtension___redArg___closed__0));
v___x_183_ = lean_mk_io_user_error(v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension___redArg(lean_object* v_mkInitial_184_){
_start:
{
uint8_t v___x_186_; 
v___x_186_ = l_Lean_initializing();
if (v___x_186_ == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; 
lean_dec_ref(v_mkInitial_184_);
v___x_187_ = lean_obj_once(&l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1, &l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1_once, _init_l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1);
v___x_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
return v___x_188_;
}
else
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_189_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef;
v___x_190_ = lean_st_ref_get(v___x_189_);
v___x_191_ = lean_array_get_size(v___x_190_);
lean_dec(v___x_190_);
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v_mkInitial_184_);
v___x_193_ = lean_st_ref_take(v___x_189_);
lean_inc_ref(v___x_192_);
v___x_194_ = lean_array_push(v___x_193_, v___x_192_);
v___x_195_ = lean_st_ref_put(v___x_189_, v___x_194_);
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_192_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension___redArg___boxed(lean_object* v_mkInitial_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_Meta_Sym_registerSymExtension___redArg(v_mkInitial_197_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension(lean_object* v_00_u03c3_200_, lean_object* v_mkInitial_201_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Meta_Sym_registerSymExtension___redArg(v_mkInitial_201_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension___boxed(lean_object* v_00_u03c3_204_, lean_object* v_mkInitial_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_Meta_Sym_registerSymExtension(v_00_u03c3_204_, v_mkInitial_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(size_t v_sz_208_, size_t v_i_209_, lean_object* v_bs_210_){
_start:
{
uint8_t v___x_212_; 
v___x_212_ = lean_usize_dec_lt(v_i_209_, v_sz_208_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; 
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v_bs_210_);
return v___x_213_;
}
else
{
lean_object* v_v_214_; lean_object* v_mkInitial_215_; lean_object* v___x_216_; lean_object* v_bs_x27_217_; lean_object* v___x_218_; 
v_v_214_ = lean_array_uget_borrowed(v_bs_210_, v_i_209_);
v_mkInitial_215_ = lean_ctor_get(v_v_214_, 1);
lean_inc_ref(v_mkInitial_215_);
v___x_216_ = lean_unsigned_to_nat(0u);
v_bs_x27_217_ = lean_array_uset(v_bs_210_, v_i_209_, v___x_216_);
v___x_218_ = lean_apply_1(v_mkInitial_215_, lean_box(0));
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; size_t v___x_220_; size_t v___x_221_; lean_object* v___x_222_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_a_219_);
lean_dec_ref_known(v___x_218_, 1);
v___x_220_ = ((size_t)1ULL);
v___x_221_ = lean_usize_add(v_i_209_, v___x_220_);
v___x_222_ = lean_array_uset(v_bs_x27_217_, v_i_209_, v_a_219_);
v_i_209_ = v___x_221_;
v_bs_210_ = v___x_222_;
goto _start;
}
else
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
lean_dec_ref(v_bs_x27_217_);
v_a_224_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_231_ == 0)
{
v___x_226_ = v___x_218_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_218_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_224_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0___boxed(lean_object* v_sz_232_, lean_object* v_i_233_, lean_object* v_bs_234_, lean_object* v___y_235_){
_start:
{
size_t v_sz_boxed_236_; size_t v_i_boxed_237_; lean_object* v_res_238_; 
v_sz_boxed_236_ = lean_unbox_usize(v_sz_232_);
lean_dec(v_sz_232_);
v_i_boxed_237_ = lean_unbox_usize(v_i_233_);
lean_dec(v_i_233_);
v_res_238_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(v_sz_boxed_236_, v_i_boxed_237_, v_bs_234_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtensions_mkInitialStates(){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; size_t v_sz_242_; size_t v___x_243_; lean_object* v___x_244_; 
v___x_240_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef;
v___x_241_ = lean_st_ref_get(v___x_240_);
v_sz_242_ = lean_array_size(v___x_241_);
v___x_243_ = ((size_t)0ULL);
v___x_244_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(v_sz_242_, v___x_243_, v___x_241_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtensions_mkInitialStates___boxed(lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx___impl(lean_object* v_x_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = lean_obj_tag_nat(v_x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx___impl___boxed(lean_object* v_x_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Meta_Sym_CongrInfo_ctorIdx___impl(v_x_257_);
lean_dec(v_x_257_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(lean_object* v_t_259_, lean_object* v_k_260_){
_start:
{
switch(lean_obj_tag(v_t_259_))
{
case 0:
{
return v_k_260_;
}
case 1:
{
lean_object* v_prefixSize_261_; lean_object* v_suffixSize_262_; lean_object* v___x_263_; 
v_prefixSize_261_ = lean_ctor_get(v_t_259_, 0);
lean_inc(v_prefixSize_261_);
v_suffixSize_262_ = lean_ctor_get(v_t_259_, 1);
lean_inc(v_suffixSize_262_);
lean_dec_ref_known(v_t_259_, 2);
v___x_263_ = lean_apply_2(v_k_260_, v_prefixSize_261_, v_suffixSize_262_);
return v___x_263_;
}
default: 
{
lean_object* v_rewritable_264_; lean_object* v___x_265_; 
v_rewritable_264_ = lean_ctor_get(v_t_259_, 0);
lean_inc_ref(v_rewritable_264_);
lean_dec(v_t_259_);
v___x_265_ = lean_apply_1(v_k_260_, v_rewritable_264_);
return v___x_265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim(lean_object* v_motive_266_, lean_object* v_ctorIdx_267_, lean_object* v_t_268_, lean_object* v_h_269_, lean_object* v_k_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_268_, v_k_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim___boxed(lean_object* v_motive_272_, lean_object* v_ctorIdx_273_, lean_object* v_t_274_, lean_object* v_h_275_, lean_object* v_k_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Meta_Sym_CongrInfo_ctorElim(v_motive_272_, v_ctorIdx_273_, v_t_274_, v_h_275_, v_k_276_);
lean_dec(v_ctorIdx_273_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_none_elim___redArg(lean_object* v_t_278_, lean_object* v_none_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_278_, v_none_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_none_elim(lean_object* v_motive_281_, lean_object* v_t_282_, lean_object* v_h_283_, lean_object* v_none_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_282_, v_none_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim___redArg(lean_object* v_t_286_, lean_object* v_fixedPrefix_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_286_, v_fixedPrefix_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim(lean_object* v_motive_289_, lean_object* v_t_290_, lean_object* v_h_291_, lean_object* v_fixedPrefix_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_290_, v_fixedPrefix_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_interlaced_elim___redArg(lean_object* v_t_294_, lean_object* v_interlaced_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_294_, v_interlaced_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_interlaced_elim(lean_object* v_motive_297_, lean_object* v_t_298_, lean_object* v_h_299_, lean_object* v_interlaced_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_298_, v_interlaced_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim___redArg(lean_object* v_t_302_, lean_object* v_congrTheorem_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_302_, v_congrTheorem_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim(lean_object* v_motive_305_, lean_object* v_t_306_, lean_object* v_h_307_, lean_object* v_congrTheorem_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_306_, v_congrTheorem_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducibleStep(lean_object* v_e_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_Expr_getAppFn(v_e_316_);
if (lean_obj_tag(v___x_322_) == 4)
{
lean_object* v_declName_323_; lean_object* v___x_324_; lean_object* v_env_325_; uint8_t v___x_326_; 
v_declName_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_declName_323_);
lean_dec_ref_known(v___x_322_, 2);
v___x_324_ = lean_st_ref_get(v_a_320_);
v_env_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc_ref(v_env_325_);
lean_dec(v___x_324_);
v___x_326_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_325_, v_declName_323_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; 
lean_dec_ref(v_e_316_);
v___x_327_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
else
{
uint8_t v___x_329_; lean_object* v___x_330_; 
v___x_329_ = 0;
v___x_330_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_316_, v___x_329_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_350_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_350_ == 0)
{
v___x_333_ = v___x_330_;
v_isShared_334_ = v_isSharedCheck_350_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_350_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
if (lean_obj_tag(v_a_331_) == 1)
{
lean_object* v_val_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_345_; 
v_val_335_ = lean_ctor_get(v_a_331_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v_a_331_);
if (v_isSharedCheck_345_ == 0)
{
v___x_337_ = v_a_331_;
v_isShared_338_ = v_isSharedCheck_345_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_val_335_);
lean_dec(v_a_331_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_345_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_val_335_);
v___x_340_ = v_reuseFailAlloc_344_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_342_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_340_);
v___x_342_ = v___x_333_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
else
{
lean_object* v___x_346_; lean_object* v___x_348_; 
lean_dec(v_a_331_);
v___x_346_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_346_);
v___x_348_ = v___x_333_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
v_a_351_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_330_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_330_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; 
lean_dec_ref(v___x_322_);
lean_dec_ref(v_e_316_);
v___x_359_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducibleStep___boxed(lean_object* v_e_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_Meta_Sym_unfoldReducibleStep(v_e_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
return v_res_367_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0(lean_object* v_env_368_, lean_object* v_e_369_){
_start:
{
if (lean_obj_tag(v_e_369_) == 4)
{
lean_object* v_declName_370_; uint8_t v___x_371_; 
v_declName_370_ = lean_ctor_get(v_e_369_, 0);
lean_inc(v_declName_370_);
lean_dec_ref_known(v_e_369_, 2);
v___x_371_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_368_, v_declName_370_);
return v___x_371_;
}
else
{
uint8_t v___x_372_; 
lean_dec_ref(v_e_369_);
lean_dec_ref(v_env_368_);
v___x_372_ = 0;
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0___boxed(lean_object* v_env_373_, lean_object* v_e_374_){
_start:
{
uint8_t v_res_375_; lean_object* v_r_376_; 
v_res_375_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0(v_env_373_, v_e_374_);
v_r_376_ = lean_box(v_res_375_);
return v_r_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(lean_object* v_e_377_, lean_object* v_a_378_){
_start:
{
lean_object* v___x_380_; lean_object* v_env_381_; lean_object* v___f_382_; lean_object* v___x_383_; 
v___x_380_ = lean_st_ref_get(v_a_378_);
v_env_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc_ref(v_env_381_);
lean_dec(v___x_380_);
v___f_382_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_382_, 0, v_env_381_);
v___x_383_ = lean_find_expr(v___f_382_, v_e_377_);
lean_dec_ref(v___f_382_);
if (lean_obj_tag(v___x_383_) == 0)
{
uint8_t v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = 0;
v___x_385_ = lean_box(v___x_384_);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
else
{
lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_395_; 
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_395_ == 0)
{
lean_object* v_unused_396_; 
v_unused_396_ = lean_ctor_get(v___x_383_, 0);
lean_dec(v_unused_396_);
v___x_388_ = v___x_383_;
v_isShared_389_ = v_isSharedCheck_395_;
goto v_resetjp_387_;
}
else
{
lean_dec(v___x_383_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_395_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
uint8_t v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_390_ = 1;
v___x_391_ = lean_box(v___x_390_);
if (v_isShared_389_ == 0)
{
lean_ctor_set_tag(v___x_388_, 0);
lean_ctor_set(v___x_388_, 0, v___x_391_);
v___x_393_ = v___x_388_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___boxed(lean_object* v_e_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_397_, v_a_398_);
lean_dec(v_a_398_);
lean_dec_ref(v_e_397_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget(lean_object* v_e_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_401_, v_a_403_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___boxed(lean_object* v_e_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget(v_e_406_, v_a_407_, v_a_408_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec_ref(v_e_406_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___lam__0(lean_object* v_e_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_417_, 0, v_e_411_);
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___lam__0___boxed(lean_object* v_e_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Meta_Sym_unfoldReducible___lam__0(v_e_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__1(lean_object* v_x_426_, lean_object* v_e_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v_e_427_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__1___boxed(lean_object* v_x_434_, lean_object* v_e_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__1(v_x_434_, v_e_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec_ref(v_x_434_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_object* v_00_u03b1_442_, lean_object* v_x_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_apply_1(v_x_443_, lean_box(0));
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0___boxed(lean_object* v_00_u03b1_451_, lean_object* v_x_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(v_00_u03b1_451_, v_x_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
return v_res_458_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(lean_object* v_a_459_, lean_object* v_x_460_){
_start:
{
if (lean_obj_tag(v_x_460_) == 0)
{
uint8_t v___x_461_; 
v___x_461_ = 0;
return v___x_461_;
}
else
{
lean_object* v_key_462_; lean_object* v_tail_463_; uint8_t v___x_464_; 
v_key_462_ = lean_ctor_get(v_x_460_, 0);
v_tail_463_ = lean_ctor_get(v_x_460_, 2);
v___x_464_ = l_Lean_ExprStructEq_beq(v_key_462_, v_a_459_);
if (v___x_464_ == 0)
{
v_x_460_ = v_tail_463_;
goto _start;
}
else
{
return v___x_464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object* v_a_466_, lean_object* v_x_467_){
_start:
{
uint8_t v_res_468_; lean_object* v_r_469_; 
v_res_468_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_466_, v_x_467_);
lean_dec(v_x_467_);
lean_dec_ref(v_a_466_);
v_r_469_ = lean_box(v_res_468_);
return v_r_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object* v_x_470_, lean_object* v_x_471_){
_start:
{
if (lean_obj_tag(v_x_471_) == 0)
{
return v_x_470_;
}
else
{
lean_object* v_key_472_; lean_object* v_value_473_; lean_object* v_tail_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_497_; 
v_key_472_ = lean_ctor_get(v_x_471_, 0);
v_value_473_ = lean_ctor_get(v_x_471_, 1);
v_tail_474_ = lean_ctor_get(v_x_471_, 2);
v_isSharedCheck_497_ = !lean_is_exclusive(v_x_471_);
if (v_isSharedCheck_497_ == 0)
{
v___x_476_ = v_x_471_;
v_isShared_477_ = v_isSharedCheck_497_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_tail_474_);
lean_inc(v_value_473_);
lean_inc(v_key_472_);
lean_dec(v_x_471_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_497_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; uint64_t v___x_479_; uint64_t v___x_480_; uint64_t v___x_481_; uint64_t v_fold_482_; uint64_t v___x_483_; uint64_t v___x_484_; uint64_t v___x_485_; size_t v___x_486_; size_t v___x_487_; size_t v___x_488_; size_t v___x_489_; size_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_478_ = lean_array_get_size(v_x_470_);
v___x_479_ = l_Lean_ExprStructEq_hash(v_key_472_);
v___x_480_ = 32ULL;
v___x_481_ = lean_uint64_shift_right(v___x_479_, v___x_480_);
v_fold_482_ = lean_uint64_xor(v___x_479_, v___x_481_);
v___x_483_ = 16ULL;
v___x_484_ = lean_uint64_shift_right(v_fold_482_, v___x_483_);
v___x_485_ = lean_uint64_xor(v_fold_482_, v___x_484_);
v___x_486_ = lean_uint64_to_usize(v___x_485_);
v___x_487_ = lean_usize_of_nat(v___x_478_);
v___x_488_ = ((size_t)1ULL);
v___x_489_ = lean_usize_sub(v___x_487_, v___x_488_);
v___x_490_ = lean_usize_land(v___x_486_, v___x_489_);
v___x_491_ = lean_array_uget_borrowed(v_x_470_, v___x_490_);
lean_inc(v___x_491_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 2, v___x_491_);
v___x_493_ = v___x_476_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_key_472_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_value_473_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v___x_491_);
v___x_493_ = v_reuseFailAlloc_496_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_494_; 
v___x_494_ = lean_array_uset(v_x_470_, v___x_490_, v___x_493_);
v_x_470_ = v___x_494_;
v_x_471_ = v_tail_474_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object* v_i_498_, lean_object* v_source_499_, lean_object* v_target_500_){
_start:
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = lean_array_get_size(v_source_499_);
v___x_502_ = lean_nat_dec_lt(v_i_498_, v___x_501_);
if (v___x_502_ == 0)
{
lean_dec_ref(v_source_499_);
lean_dec(v_i_498_);
return v_target_500_;
}
else
{
lean_object* v_es_503_; lean_object* v___x_504_; lean_object* v_source_505_; lean_object* v_target_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v_es_503_ = lean_array_fget(v_source_499_, v_i_498_);
v___x_504_ = lean_box(0);
v_source_505_ = lean_array_fset(v_source_499_, v_i_498_, v___x_504_);
v_target_506_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_500_, v_es_503_);
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = lean_nat_add(v_i_498_, v___x_507_);
lean_dec(v_i_498_);
v_i_498_ = v___x_508_;
v_source_499_ = v_source_505_;
v_target_500_ = v_target_506_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(lean_object* v_data_510_){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v_nbuckets_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_511_ = lean_array_get_size(v_data_510_);
v___x_512_ = lean_unsigned_to_nat(2u);
v_nbuckets_513_ = lean_nat_mul(v___x_511_, v___x_512_);
v___x_514_ = lean_unsigned_to_nat(0u);
v___x_515_ = lean_box(0);
v___x_516_ = lean_mk_array(v_nbuckets_513_, v___x_515_);
v___x_517_ = lean_array_propagate_mark(v_data_510_, v___x_516_);
v___x_518_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_514_, v_data_510_, v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(lean_object* v_a_519_, lean_object* v_b_520_, lean_object* v_x_521_){
_start:
{
if (lean_obj_tag(v_x_521_) == 0)
{
lean_dec(v_b_520_);
lean_dec_ref(v_a_519_);
return v_x_521_;
}
else
{
lean_object* v_key_522_; lean_object* v_value_523_; lean_object* v_tail_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_536_; 
v_key_522_ = lean_ctor_get(v_x_521_, 0);
v_value_523_ = lean_ctor_get(v_x_521_, 1);
v_tail_524_ = lean_ctor_get(v_x_521_, 2);
v_isSharedCheck_536_ = !lean_is_exclusive(v_x_521_);
if (v_isSharedCheck_536_ == 0)
{
v___x_526_ = v_x_521_;
v_isShared_527_ = v_isSharedCheck_536_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_tail_524_);
lean_inc(v_value_523_);
lean_inc(v_key_522_);
lean_dec(v_x_521_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_536_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
uint8_t v___x_528_; 
v___x_528_ = l_Lean_ExprStructEq_beq(v_key_522_, v_a_519_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_529_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_519_, v_b_520_, v_tail_524_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 2, v___x_529_);
v___x_531_ = v___x_526_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_key_522_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_value_523_);
lean_ctor_set(v_reuseFailAlloc_532_, 2, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
else
{
lean_object* v___x_534_; 
lean_dec(v_value_523_);
lean_dec(v_key_522_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 1, v_b_520_);
lean_ctor_set(v___x_526_, 0, v_a_519_);
v___x_534_ = v___x_526_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_519_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_b_520_);
lean_ctor_set(v_reuseFailAlloc_535_, 2, v_tail_524_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(lean_object* v_m_537_, lean_object* v_a_538_, lean_object* v_b_539_){
_start:
{
lean_object* v_size_540_; lean_object* v_buckets_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_584_; 
v_size_540_ = lean_ctor_get(v_m_537_, 0);
v_buckets_541_ = lean_ctor_get(v_m_537_, 1);
v_isSharedCheck_584_ = !lean_is_exclusive(v_m_537_);
if (v_isSharedCheck_584_ == 0)
{
v___x_543_ = v_m_537_;
v_isShared_544_ = v_isSharedCheck_584_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_buckets_541_);
lean_inc(v_size_540_);
lean_dec(v_m_537_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_584_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; uint64_t v___x_546_; uint64_t v___x_547_; uint64_t v___x_548_; uint64_t v_fold_549_; uint64_t v___x_550_; uint64_t v___x_551_; uint64_t v___x_552_; size_t v___x_553_; size_t v___x_554_; size_t v___x_555_; size_t v___x_556_; size_t v___x_557_; lean_object* v_bkt_558_; uint8_t v___x_559_; 
v___x_545_ = lean_array_get_size(v_buckets_541_);
v___x_546_ = l_Lean_ExprStructEq_hash(v_a_538_);
v___x_547_ = 32ULL;
v___x_548_ = lean_uint64_shift_right(v___x_546_, v___x_547_);
v_fold_549_ = lean_uint64_xor(v___x_546_, v___x_548_);
v___x_550_ = 16ULL;
v___x_551_ = lean_uint64_shift_right(v_fold_549_, v___x_550_);
v___x_552_ = lean_uint64_xor(v_fold_549_, v___x_551_);
v___x_553_ = lean_uint64_to_usize(v___x_552_);
v___x_554_ = lean_usize_of_nat(v___x_545_);
v___x_555_ = ((size_t)1ULL);
v___x_556_ = lean_usize_sub(v___x_554_, v___x_555_);
v___x_557_ = lean_usize_land(v___x_553_, v___x_556_);
v_bkt_558_ = lean_array_uget_borrowed(v_buckets_541_, v___x_557_);
v___x_559_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_538_, v_bkt_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v_size_x27_561_; lean_object* v___x_562_; lean_object* v_buckets_x27_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_560_ = lean_unsigned_to_nat(1u);
v_size_x27_561_ = lean_nat_add(v_size_540_, v___x_560_);
lean_dec(v_size_540_);
lean_inc(v_bkt_558_);
v___x_562_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_562_, 0, v_a_538_);
lean_ctor_set(v___x_562_, 1, v_b_539_);
lean_ctor_set(v___x_562_, 2, v_bkt_558_);
v_buckets_x27_563_ = lean_array_uset(v_buckets_541_, v___x_557_, v___x_562_);
v___x_564_ = lean_unsigned_to_nat(4u);
v___x_565_ = lean_nat_mul(v_size_x27_561_, v___x_564_);
v___x_566_ = lean_unsigned_to_nat(3u);
v___x_567_ = lean_nat_div(v___x_565_, v___x_566_);
lean_dec(v___x_565_);
v___x_568_ = lean_array_get_size(v_buckets_x27_563_);
v___x_569_ = lean_nat_dec_le(v___x_567_, v___x_568_);
lean_dec(v___x_567_);
if (v___x_569_ == 0)
{
lean_object* v_val_570_; lean_object* v___x_572_; 
v_val_570_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_563_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 1, v_val_570_);
lean_ctor_set(v___x_543_, 0, v_size_x27_561_);
v___x_572_ = v___x_543_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_size_x27_561_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_val_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
else
{
lean_object* v___x_575_; 
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 1, v_buckets_x27_563_);
lean_ctor_set(v___x_543_, 0, v_size_x27_561_);
v___x_575_ = v___x_543_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_size_x27_561_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_buckets_x27_563_);
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
lean_object* v___x_577_; lean_object* v_buckets_x27_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
lean_inc(v_bkt_558_);
v___x_577_ = lean_box(0);
v_buckets_x27_578_ = lean_array_uset(v_buckets_541_, v___x_557_, v___x_577_);
v___x_579_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_538_, v_b_539_, v_bkt_558_);
v___x_580_ = lean_array_uset(v_buckets_x27_578_, v___x_557_, v___x_579_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 1, v___x_580_);
v___x_582_ = v___x_543_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_size_540_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(lean_object* v_a_585_, lean_object* v_e_586_, lean_object* v_a_587_){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_589_ = lean_st_ref_take(v_a_585_);
v___x_590_ = lean_box(0);
v___x_591_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v___x_589_, v_e_586_, v_a_587_);
v___x_592_ = lean_st_ref_put(v_a_585_, v___x_591_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed(lean_object* v_a_593_, lean_object* v_e_594_, lean_object* v_a_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(v_a_593_, v_e_594_, v_a_595_);
lean_dec(v_a_593_);
return v_res_597_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = l_Lean_maxRecDepthErrorMessage;
v___x_604_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
return v___x_604_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
v___x_606_ = l_Lean_MessageData_ofFormat(v___x_605_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
v___x_608_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2));
v___x_609_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set(v___x_609_, 1, v___x_607_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(lean_object* v_ref_610_){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_612_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_613_, 0, v_ref_610_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object* v_ref_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_615_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(lean_object* v_x_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___y_626_; lean_object* v_toCold_635_; lean_object* v_currRecDepth_636_; lean_object* v_ref_637_; uint16_t v_optionFlags_638_; uint8_t v_suppressElabErrors_639_; uint8_t v_isRecordingDeps_640_; lean_object* v_maxRecDepth_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v_toCold_635_ = lean_ctor_get(v___y_622_, 0);
v_currRecDepth_636_ = lean_ctor_get(v___y_622_, 1);
v_ref_637_ = lean_ctor_get(v___y_622_, 2);
v_optionFlags_638_ = lean_ctor_get_uint16(v___y_622_, sizeof(void*)*3);
v_suppressElabErrors_639_ = lean_ctor_get_uint8(v___y_622_, sizeof(void*)*3 + 2);
v_isRecordingDeps_640_ = lean_ctor_get_uint8(v___y_622_, sizeof(void*)*3 + 3);
v_maxRecDepth_646_ = lean_ctor_get(v_toCold_635_, 3);
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = lean_nat_dec_eq(v_maxRecDepth_646_, v___x_647_);
if (v___x_648_ == 0)
{
uint8_t v___x_649_; 
v___x_649_ = lean_nat_dec_eq(v_currRecDepth_636_, v_maxRecDepth_646_);
if (v___x_649_ == 0)
{
goto v___jp_641_;
}
else
{
lean_object* v___x_650_; 
lean_dec_ref(v_x_618_);
lean_inc(v_ref_637_);
v___x_650_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_637_);
v___y_626_ = v___x_650_;
goto v___jp_625_;
}
}
else
{
goto v___jp_641_;
}
v___jp_625_:
{
if (lean_obj_tag(v___y_626_) == 0)
{
return v___y_626_;
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
v_a_627_ = lean_ctor_get(v___y_626_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___y_626_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___y_626_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___y_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
v___jp_641_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_642_ = lean_unsigned_to_nat(1u);
v___x_643_ = lean_nat_add(v_currRecDepth_636_, v___x_642_);
lean_inc(v_ref_637_);
lean_inc_ref(v_toCold_635_);
v___x_644_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_644_, 0, v_toCold_635_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
lean_ctor_set(v___x_644_, 2, v_ref_637_);
lean_ctor_set_uint16(v___x_644_, sizeof(void*)*3, v_optionFlags_638_);
lean_ctor_set_uint8(v___x_644_, sizeof(void*)*3 + 2, v_suppressElabErrors_639_);
lean_ctor_set_uint8(v___x_644_, sizeof(void*)*3 + 3, v_isRecordingDeps_640_);
lean_inc(v___y_623_);
lean_inc(v___y_621_);
lean_inc_ref(v___y_620_);
lean_inc(v___y_619_);
v___x_645_ = lean_apply_6(v_x_618_, v___y_619_, v___y_620_, v___y_621_, v___x_644_, v___y_623_, lean_box(0));
v___y_626_ = v___x_645_;
goto v___jp_625_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg___boxed(lean_object* v_x_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_659_, lean_object* v_x_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_apply_1(v_x_660_, lean_box(0));
v___x_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_668_, lean_object* v_x_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(v_00_u03b1_668_, v_x_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_a_676_, lean_object* v_x_677_){
_start:
{
if (lean_obj_tag(v_x_677_) == 0)
{
lean_object* v___x_678_; 
v___x_678_ = lean_box(0);
return v___x_678_;
}
else
{
lean_object* v_key_679_; lean_object* v_value_680_; lean_object* v_tail_681_; uint8_t v___x_682_; 
v_key_679_ = lean_ctor_get(v_x_677_, 0);
v_value_680_ = lean_ctor_get(v_x_677_, 1);
v_tail_681_ = lean_ctor_get(v_x_677_, 2);
v___x_682_ = l_Lean_ExprStructEq_beq(v_key_679_, v_a_676_);
if (v___x_682_ == 0)
{
v_x_677_ = v_tail_681_;
goto _start;
}
else
{
lean_object* v___x_684_; 
lean_inc(v_value_680_);
v___x_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_684_, 0, v_value_680_);
return v___x_684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_a_685_, lean_object* v_x_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_spec__2___redArg(v_a_685_, v_x_686_);
lean_dec(v_x_686_);
lean_dec_ref(v_a_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___redArg(lean_object* v_m_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_buckets_690_; lean_object* v___x_691_; uint64_t v___x_692_; uint64_t v___x_693_; uint64_t v___x_694_; uint64_t v_fold_695_; uint64_t v___x_696_; uint64_t v___x_697_; uint64_t v___x_698_; size_t v___x_699_; size_t v___x_700_; size_t v___x_701_; size_t v___x_702_; size_t v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_buckets_690_ = lean_ctor_get(v_m_688_, 1);
v___x_691_ = lean_array_get_size(v_buckets_690_);
v___x_692_ = l_Lean_ExprStructEq_hash(v_a_689_);
v___x_693_ = 32ULL;
v___x_694_ = lean_uint64_shift_right(v___x_692_, v___x_693_);
v_fold_695_ = lean_uint64_xor(v___x_692_, v___x_694_);
v___x_696_ = 16ULL;
v___x_697_ = lean_uint64_shift_right(v_fold_695_, v___x_696_);
v___x_698_ = lean_uint64_xor(v_fold_695_, v___x_697_);
v___x_699_ = lean_uint64_to_usize(v___x_698_);
v___x_700_ = lean_usize_of_nat(v___x_691_);
v___x_701_ = ((size_t)1ULL);
v___x_702_ = lean_usize_sub(v___x_700_, v___x_701_);
v___x_703_ = lean_usize_land(v___x_699_, v___x_702_);
v___x_704_ = lean_array_uget_borrowed(v_buckets_690_, v___x_703_);
v___x_705_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_spec__2___redArg(v_a_689_, v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_706_, lean_object* v_a_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___redArg(v_m_706_, v_a_707_);
lean_dec_ref(v_a_707_);
lean_dec_ref(v_m_706_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__2(lean_object* v___x_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_709_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__2___boxed(lean_object* v___x_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__2(v___x_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object* v_k_723_, lean_object* v___y_724_, lean_object* v_b_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; 
lean_inc(v___y_729_);
lean_inc_ref(v___y_728_);
lean_inc(v___y_727_);
lean_inc_ref(v___y_726_);
lean_inc(v___y_724_);
v___x_731_ = lean_apply_7(v_k_723_, v_b_725_, v___y_724_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, lean_box(0));
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_732_, lean_object* v___y_733_, lean_object* v_b_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_732_, v___y_733_, v_b_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_733_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_name_741_, uint8_t v_bi_742_, lean_object* v_type_743_, lean_object* v_k_744_, uint8_t v_kind_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v___f_752_; lean_object* v___x_753_; 
lean_inc(v___y_746_);
v___f_752_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_752_, 0, v_k_744_);
lean_closure_set(v___f_752_, 1, v___y_746_);
v___x_753_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_741_, v_bi_742_, v_type_743_, v___f_752_, v_kind_745_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_753_) == 0)
{
return v___x_753_;
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_753_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_753_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_name_762_, lean_object* v_bi_763_, lean_object* v_type_764_, lean_object* v_k_765_, lean_object* v_kind_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
uint8_t v_bi_boxed_773_; uint8_t v_kind_boxed_774_; lean_object* v_res_775_; 
v_bi_boxed_773_ = lean_unbox(v_bi_763_);
v_kind_boxed_774_ = lean_unbox(v_kind_766_);
v_res_775_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_762_, v_bi_boxed_773_, v_type_764_, v_k_765_, v_kind_boxed_774_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(lean_object* v_name_776_, lean_object* v_type_777_, lean_object* v_val_778_, lean_object* v_k_779_, uint8_t v_nondep_780_, uint8_t v_kind_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v___f_788_; lean_object* v___x_789_; 
lean_inc(v___y_782_);
v___f_788_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_788_, 0, v_k_779_);
lean_closure_set(v___f_788_, 1, v___y_782_);
v___x_789_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_776_, v_type_777_, v_val_778_, v___f_788_, v_nondep_780_, v_kind_781_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
if (lean_obj_tag(v___x_789_) == 0)
{
return v___x_789_;
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_789_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_789_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object* v_name_798_, lean_object* v_type_799_, lean_object* v_val_800_, lean_object* v_k_801_, lean_object* v_nondep_802_, lean_object* v_kind_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
uint8_t v_nondep_boxed_810_; uint8_t v_kind_boxed_811_; lean_object* v_res_812_; 
v_nondep_boxed_810_ = lean_unbox(v_nondep_802_);
v_kind_boxed_811_ = lean_unbox(v_kind_803_);
v_res_812_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_798_, v_type_799_, v_val_800_, v_k_801_, v_nondep_boxed_810_, v_kind_boxed_811_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed(lean_object* v_fvars_813_, lean_object* v_pre_814_, lean_object* v_post_815_, lean_object* v_usedLetOnly_816_, lean_object* v_skipConstInApp_817_, lean_object* v_skipInstances_818_, lean_object* v_postApp_819_, lean_object* v_body_820_, lean_object* v_x_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
uint8_t v_usedLetOnly_boxed_828_; uint8_t v_skipConstInApp_boxed_829_; uint8_t v_skipInstances_boxed_830_; lean_object* v_res_831_; 
v_usedLetOnly_boxed_828_ = lean_unbox(v_usedLetOnly_816_);
v_skipConstInApp_boxed_829_ = lean_unbox(v_skipConstInApp_817_);
v_skipInstances_boxed_830_ = lean_unbox(v_skipInstances_818_);
v_res_831_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(v_fvars_813_, v_pre_814_, v_post_815_, v_usedLetOnly_boxed_828_, v_skipConstInApp_boxed_829_, v_skipInstances_boxed_830_, v_postApp_819_, v_body_820_, v_x_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(lean_object* v_fvars_835_, lean_object* v_pre_836_, lean_object* v_post_837_, uint8_t v_usedLetOnly_838_, uint8_t v_skipConstInApp_839_, uint8_t v_skipInstances_840_, lean_object* v_postApp_841_, lean_object* v_body_842_, lean_object* v_x_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_array_push(v_fvars_835_, v_x_843_);
v___x_851_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_836_, v_post_837_, v_usedLetOnly_838_, v_skipConstInApp_839_, v_skipInstances_840_, v_postApp_841_, v___x_850_, v_body_842_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed(lean_object* v_fvars_852_, lean_object* v_pre_853_, lean_object* v_post_854_, lean_object* v_usedLetOnly_855_, lean_object* v_skipConstInApp_856_, lean_object* v_skipInstances_857_, lean_object* v_postApp_858_, lean_object* v_body_859_, lean_object* v_x_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
uint8_t v_usedLetOnly_boxed_867_; uint8_t v_skipConstInApp_boxed_868_; uint8_t v_skipInstances_boxed_869_; lean_object* v_res_870_; 
v_usedLetOnly_boxed_867_ = lean_unbox(v_usedLetOnly_855_);
v_skipConstInApp_boxed_868_ = lean_unbox(v_skipConstInApp_856_);
v_skipInstances_boxed_869_ = lean_unbox(v_skipInstances_857_);
v_res_870_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(v_fvars_852_, v_pre_853_, v_post_854_, v_usedLetOnly_boxed_867_, v_skipConstInApp_boxed_868_, v_skipInstances_boxed_869_, v_postApp_858_, v_body_859_, v_x_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(lean_object* v_pre_871_, lean_object* v_post_872_, uint8_t v_usedLetOnly_873_, uint8_t v_skipConstInApp_874_, uint8_t v_skipInstances_875_, lean_object* v_postApp_876_, lean_object* v_e_877_, lean_object* v_a_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v___x_884_; 
lean_inc_ref(v_post_872_);
lean_inc(v___y_882_);
lean_inc_ref(v___y_881_);
lean_inc(v___y_880_);
lean_inc_ref(v___y_879_);
lean_inc_ref(v_e_877_);
v___x_884_ = lean_apply_6(v_post_872_, v_e_877_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, lean_box(0));
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_903_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_903_ == 0)
{
v___x_887_ = v___x_884_;
v_isShared_888_ = v_isSharedCheck_903_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_884_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_903_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
switch(lean_obj_tag(v_a_885_))
{
case 0:
{
lean_object* v_e_889_; lean_object* v___x_891_; 
lean_dec_ref(v_e_877_);
lean_dec_ref(v_postApp_876_);
lean_dec_ref(v_post_872_);
lean_dec_ref(v_pre_871_);
v_e_889_ = lean_ctor_get(v_a_885_, 0);
lean_inc_ref(v_e_889_);
lean_dec_ref_known(v_a_885_, 1);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v_e_889_);
v___x_891_ = v___x_887_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_e_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
case 1:
{
lean_object* v_e_893_; lean_object* v___x_894_; 
lean_del_object(v___x_887_);
lean_dec_ref(v_e_877_);
v_e_893_ = lean_ctor_get(v_a_885_, 0);
lean_inc_ref(v_e_893_);
lean_dec_ref_known(v_a_885_, 1);
v___x_894_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_871_, v_post_872_, v_usedLetOnly_873_, v_skipConstInApp_874_, v_skipInstances_875_, v_postApp_876_, v_e_893_, v_a_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
return v___x_894_;
}
default: 
{
lean_object* v_e_x3f_895_; 
lean_dec_ref(v_postApp_876_);
lean_dec_ref(v_post_872_);
lean_dec_ref(v_pre_871_);
v_e_x3f_895_ = lean_ctor_get(v_a_885_, 0);
lean_inc(v_e_x3f_895_);
lean_dec_ref_known(v_a_885_, 1);
if (lean_obj_tag(v_e_x3f_895_) == 0)
{
lean_object* v___x_897_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v_e_877_);
v___x_897_ = v___x_887_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_e_877_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
else
{
lean_object* v_val_899_; lean_object* v___x_901_; 
lean_dec_ref(v_e_877_);
v_val_899_ = lean_ctor_get(v_e_x3f_895_, 0);
lean_inc(v_val_899_);
lean_dec_ref_known(v_e_x3f_895_, 1);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v_val_899_);
v___x_901_ = v___x_887_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_val_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_dec_ref(v_e_877_);
lean_dec_ref(v_postApp_876_);
lean_dec_ref(v_post_872_);
lean_dec_ref(v_pre_871_);
v_a_904_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_884_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_884_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(lean_object* v_pre_912_, lean_object* v_post_913_, uint8_t v_usedLetOnly_914_, uint8_t v_skipConstInApp_915_, uint8_t v_skipInstances_916_, lean_object* v_postApp_917_, lean_object* v_fvars_918_, lean_object* v_e_919_, lean_object* v_a_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
if (lean_obj_tag(v_e_919_) == 6)
{
lean_object* v_binderName_926_; lean_object* v_binderType_927_; lean_object* v_body_928_; uint8_t v_binderInfo_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___f_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v_binderName_926_ = lean_ctor_get(v_e_919_, 0);
lean_inc(v_binderName_926_);
v_binderType_927_ = lean_ctor_get(v_e_919_, 1);
lean_inc_ref(v_binderType_927_);
v_body_928_ = lean_ctor_get(v_e_919_, 2);
lean_inc_ref(v_body_928_);
v_binderInfo_929_ = lean_ctor_get_uint8(v_e_919_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_919_, 3);
v___x_930_ = lean_box(v_usedLetOnly_914_);
v___x_931_ = lean_box(v_skipConstInApp_915_);
v___x_932_ = lean_box(v_skipInstances_916_);
lean_inc_ref(v_postApp_917_);
lean_inc_ref(v_post_913_);
lean_inc_ref(v_pre_912_);
lean_inc_ref(v_fvars_918_);
v___f_933_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed), 15, 8);
lean_closure_set(v___f_933_, 0, v_fvars_918_);
lean_closure_set(v___f_933_, 1, v_pre_912_);
lean_closure_set(v___f_933_, 2, v_post_913_);
lean_closure_set(v___f_933_, 3, v___x_930_);
lean_closure_set(v___f_933_, 4, v___x_931_);
lean_closure_set(v___f_933_, 5, v___x_932_);
lean_closure_set(v___f_933_, 6, v_postApp_917_);
lean_closure_set(v___f_933_, 7, v_body_928_);
v___x_934_ = lean_expr_instantiate_rev(v_binderType_927_, v_fvars_918_);
lean_dec_ref(v_fvars_918_);
lean_dec_ref(v_binderType_927_);
v___x_935_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_912_, v_post_913_, v_usedLetOnly_914_, v_skipConstInApp_915_, v_skipInstances_916_, v_postApp_917_, v___x_934_, v_a_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; uint8_t v___x_937_; lean_object* v___x_938_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
lean_dec_ref_known(v___x_935_, 1);
v___x_937_ = 0;
v___x_938_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_926_, v_binderInfo_929_, v_a_936_, v___f_933_, v___x_937_, v_a_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_938_;
}
else
{
lean_dec_ref(v___f_933_);
lean_dec(v_binderName_926_);
return v___x_935_;
}
}
else
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_expr_instantiate_rev(v_e_919_, v_fvars_918_);
lean_dec_ref(v_e_919_);
lean_inc_ref(v_postApp_917_);
lean_inc_ref(v_post_913_);
lean_inc_ref(v_pre_912_);
v___x_940_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_912_, v_post_913_, v_usedLetOnly_914_, v_skipConstInApp_915_, v_skipInstances_916_, v_postApp_917_, v___x_939_, v_a_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; uint8_t v___x_942_; uint8_t v___x_943_; uint8_t v___x_944_; lean_object* v___x_945_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
lean_dec_ref_known(v___x_940_, 1);
v___x_942_ = 0;
v___x_943_ = 1;
v___x_944_ = 1;
v___x_945_ = l_Lean_Meta_mkLambdaFVars(v_fvars_918_, v_a_941_, v___x_942_, v_usedLetOnly_914_, v___x_942_, v___x_943_, v___x_944_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec_ref(v_fvars_918_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_947_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_946_);
lean_dec_ref_known(v___x_945_, 1);
v___x_947_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_pre_912_, v_post_913_, v_usedLetOnly_914_, v_skipConstInApp_915_, v_skipInstances_916_, v_postApp_917_, v_a_946_, v_a_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_947_;
}
else
{
lean_dec_ref(v_postApp_917_);
lean_dec_ref(v_post_913_);
lean_dec_ref(v_pre_912_);
return v___x_945_;
}
}
else
{
lean_dec_ref(v_fvars_918_);
lean_dec_ref(v_postApp_917_);
lean_dec_ref(v_post_913_);
lean_dec_ref(v_pre_912_);
return v___x_940_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(lean_object* v_fvars_948_, lean_object* v_pre_949_, lean_object* v_post_950_, uint8_t v_usedLetOnly_951_, uint8_t v_skipConstInApp_952_, uint8_t v_skipInstances_953_, lean_object* v_postApp_954_, lean_object* v_body_955_, lean_object* v_x_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_array_push(v_fvars_948_, v_x_956_);
v___x_964_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_949_, v_post_950_, v_usedLetOnly_951_, v_skipConstInApp_952_, v_skipInstances_953_, v_postApp_954_, v___x_963_, v_body_955_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed(lean_object* v_fvars_965_, lean_object* v_pre_966_, lean_object* v_post_967_, lean_object* v_usedLetOnly_968_, lean_object* v_skipConstInApp_969_, lean_object* v_skipInstances_970_, lean_object* v_postApp_971_, lean_object* v_body_972_, lean_object* v_x_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
uint8_t v_usedLetOnly_boxed_980_; uint8_t v_skipConstInApp_boxed_981_; uint8_t v_skipInstances_boxed_982_; lean_object* v_res_983_; 
v_usedLetOnly_boxed_980_ = lean_unbox(v_usedLetOnly_968_);
v_skipConstInApp_boxed_981_ = lean_unbox(v_skipConstInApp_969_);
v_skipInstances_boxed_982_ = lean_unbox(v_skipInstances_970_);
v_res_983_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(v_fvars_965_, v_pre_966_, v_post_967_, v_usedLetOnly_boxed_980_, v_skipConstInApp_boxed_981_, v_skipInstances_boxed_982_, v_postApp_971_, v_body_972_, v_x_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(lean_object* v_pre_984_, lean_object* v_post_985_, uint8_t v_usedLetOnly_986_, uint8_t v_skipConstInApp_987_, uint8_t v_skipInstances_988_, lean_object* v_postApp_989_, lean_object* v_fvars_990_, lean_object* v_e_991_, lean_object* v_a_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
if (lean_obj_tag(v_e_991_) == 8)
{
lean_object* v_declName_998_; lean_object* v_type_999_; lean_object* v_value_1000_; lean_object* v_body_1001_; uint8_t v_nondep_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___f_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_declName_998_ = lean_ctor_get(v_e_991_, 0);
lean_inc(v_declName_998_);
v_type_999_ = lean_ctor_get(v_e_991_, 1);
lean_inc_ref(v_type_999_);
v_value_1000_ = lean_ctor_get(v_e_991_, 2);
lean_inc_ref(v_value_1000_);
v_body_1001_ = lean_ctor_get(v_e_991_, 3);
lean_inc_ref(v_body_1001_);
v_nondep_1002_ = lean_ctor_get_uint8(v_e_991_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_991_, 4);
v___x_1003_ = lean_box(v_usedLetOnly_986_);
v___x_1004_ = lean_box(v_skipConstInApp_987_);
v___x_1005_ = lean_box(v_skipInstances_988_);
lean_inc_ref_n(v_postApp_989_, 2);
lean_inc_ref_n(v_post_985_, 2);
lean_inc_ref_n(v_pre_984_, 2);
lean_inc_ref(v_fvars_990_);
v___f_1006_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed), 15, 8);
lean_closure_set(v___f_1006_, 0, v_fvars_990_);
lean_closure_set(v___f_1006_, 1, v_pre_984_);
lean_closure_set(v___f_1006_, 2, v_post_985_);
lean_closure_set(v___f_1006_, 3, v___x_1003_);
lean_closure_set(v___f_1006_, 4, v___x_1004_);
lean_closure_set(v___f_1006_, 5, v___x_1005_);
lean_closure_set(v___f_1006_, 6, v_postApp_989_);
lean_closure_set(v___f_1006_, 7, v_body_1001_);
v___x_1007_ = lean_expr_instantiate_rev(v_type_999_, v_fvars_990_);
lean_dec_ref(v_type_999_);
v___x_1008_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_984_, v_post_985_, v_usedLetOnly_986_, v_skipConstInApp_987_, v_skipInstances_988_, v_postApp_989_, v___x_1007_, v_a_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1008_, 1);
v___x_1010_ = lean_expr_instantiate_rev(v_value_1000_, v_fvars_990_);
lean_dec_ref(v_fvars_990_);
lean_dec_ref(v_value_1000_);
v___x_1011_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_984_, v_post_985_, v_usedLetOnly_986_, v_skipConstInApp_987_, v_skipInstances_988_, v_postApp_989_, v___x_1010_, v_a_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; uint8_t v___x_1013_; lean_object* v___x_1014_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref_known(v___x_1011_, 1);
v___x_1013_ = 0;
v___x_1014_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_998_, v_a_1009_, v_a_1012_, v___f_1006_, v_nondep_1002_, v___x_1013_, v_a_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
return v___x_1014_;
}
else
{
lean_dec(v_a_1009_);
lean_dec_ref(v___f_1006_);
lean_dec(v_declName_998_);
return v___x_1011_;
}
}
else
{
lean_dec_ref(v___f_1006_);
lean_dec_ref(v_value_1000_);
lean_dec(v_declName_998_);
lean_dec_ref(v_fvars_990_);
lean_dec_ref(v_postApp_989_);
lean_dec_ref(v_post_985_);
lean_dec_ref(v_pre_984_);
return v___x_1008_;
}
}
else
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_expr_instantiate_rev(v_e_991_, v_fvars_990_);
lean_dec_ref(v_e_991_);
lean_inc_ref(v_postApp_989_);
lean_inc_ref(v_post_985_);
lean_inc_ref(v_pre_984_);
v___x_1016_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_984_, v_post_985_, v_usedLetOnly_986_, v_skipConstInApp_987_, v_skipInstances_988_, v_postApp_989_, v___x_1015_, v_a_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; uint8_t v___x_1018_; uint8_t v___x_1019_; lean_object* v___x_1020_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1016_, 1);
v___x_1018_ = 0;
v___x_1019_ = 1;
v___x_1020_ = l_Lean_Meta_mkLetFVars(v_fvars_990_, v_a_1017_, v_usedLetOnly_986_, v___x_1018_, v___x_1019_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
lean_dec_ref(v_fvars_990_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1022_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 1);
v___x_1022_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_pre_984_, v_post_985_, v_usedLetOnly_986_, v_skipConstInApp_987_, v_skipInstances_988_, v_postApp_989_, v_a_1021_, v_a_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
return v___x_1022_;
}
else
{
lean_dec_ref(v_postApp_989_);
lean_dec_ref(v_post_985_);
lean_dec_ref(v_pre_984_);
return v___x_1020_;
}
}
else
{
lean_dec_ref(v_fvars_990_);
lean_dec_ref(v_postApp_989_);
lean_dec_ref(v_post_985_);
lean_dec_ref(v_pre_984_);
return v___x_1016_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1023_; lean_object* v_dummy_1024_; 
v___x_1023_ = lean_box(0);
v_dummy_1024_ = l_Lean_Expr_sort___override(v___x_1023_);
return v_dummy_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(lean_object* v_pre_1025_, lean_object* v_post_1026_, uint8_t v_usedLetOnly_1027_, uint8_t v_skipConstInApp_1028_, uint8_t v_skipInstances_1029_, lean_object* v_postApp_1030_, size_t v_sz_1031_, size_t v_i_1032_, lean_object* v_bs_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
uint8_t v___x_1040_; 
v___x_1040_ = lean_usize_dec_lt(v_i_1032_, v_sz_1031_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; 
lean_dec_ref(v_postApp_1030_);
lean_dec_ref(v_post_1026_);
lean_dec_ref(v_pre_1025_);
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v_bs_1033_);
return v___x_1041_;
}
else
{
lean_object* v_v_1042_; lean_object* v___x_1043_; lean_object* v_bs_x27_1044_; lean_object* v___x_1045_; 
v_v_1042_ = lean_array_uget(v_bs_1033_, v_i_1032_);
v___x_1043_ = lean_unsigned_to_nat(0u);
v_bs_x27_1044_ = lean_array_uset(v_bs_1033_, v_i_1032_, v___x_1043_);
lean_inc_ref(v_postApp_1030_);
lean_inc_ref(v_post_1026_);
lean_inc_ref(v_pre_1025_);
v___x_1045_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1025_, v_post_1026_, v_usedLetOnly_1027_, v_skipConstInApp_1028_, v_skipInstances_1029_, v_postApp_1030_, v_v_1042_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; size_t v___x_1047_; size_t v___x_1048_; lean_object* v___x_1049_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 1);
v___x_1047_ = ((size_t)1ULL);
v___x_1048_ = lean_usize_add(v_i_1032_, v___x_1047_);
v___x_1049_ = lean_array_uset(v_bs_x27_1044_, v_i_1032_, v_a_1046_);
v_i_1032_ = v___x_1048_;
v_bs_1033_ = v___x_1049_;
goto _start;
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec_ref(v_bs_x27_1044_);
lean_dec_ref(v_postApp_1030_);
lean_dec_ref(v_post_1026_);
lean_dec_ref(v_pre_1025_);
v_a_1051_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1045_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1045_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__0(lean_object* v_pre_1059_, lean_object* v_post_1060_, uint8_t v_usedLetOnly_1061_, uint8_t v_skipConstInApp_1062_, uint8_t v_skipInstances_1063_, lean_object* v_postApp_1064_, lean_object* v___x_1065_, lean_object* v___y_1066_, lean_object* v_b_1067_, lean_object* v_a_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1059_, v_post_1060_, v_usedLetOnly_1061_, v_skipConstInApp_1062_, v_skipInstances_1063_, v_postApp_1064_, v___x_1065_, v___y_1066_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1084_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1077_ = v___x_1074_;
v_isShared_1078_ = v_isSharedCheck_1084_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1074_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1084_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1079_ = lean_array_fset(v_b_1067_, v_a_1068_, v_a_1075_);
v___x_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1080_);
v___x_1082_ = v___x_1077_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec_ref(v_b_1067_);
v_a_1085_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1074_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1074_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__0___boxed(lean_object* v_pre_1093_, lean_object* v_post_1094_, lean_object* v_usedLetOnly_1095_, lean_object* v_skipConstInApp_1096_, lean_object* v_skipInstances_1097_, lean_object* v_postApp_1098_, lean_object* v___x_1099_, lean_object* v___y_1100_, lean_object* v_b_1101_, lean_object* v_a_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
uint8_t v_usedLetOnly_boxed_1108_; uint8_t v_skipConstInApp_boxed_1109_; uint8_t v_skipInstances_boxed_1110_; lean_object* v_res_1111_; 
v_usedLetOnly_boxed_1108_ = lean_unbox(v_usedLetOnly_1095_);
v_skipConstInApp_boxed_1109_ = lean_unbox(v_skipConstInApp_1096_);
v_skipInstances_boxed_1110_ = lean_unbox(v_skipInstances_1097_);
v_res_1111_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__0(v_pre_1093_, v_post_1094_, v_usedLetOnly_boxed_1108_, v_skipConstInApp_boxed_1109_, v_skipInstances_boxed_1110_, v_postApp_1098_, v___x_1099_, v___y_1100_, v_b_1101_, v_a_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v_a_1102_);
lean_dec(v___y_1100_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(lean_object* v_upperBound_1112_, lean_object* v___x_1113_, lean_object* v_pre_1114_, lean_object* v_post_1115_, uint8_t v_usedLetOnly_1116_, uint8_t v_skipConstInApp_1117_, uint8_t v_skipInstances_1118_, lean_object* v_postApp_1119_, lean_object* v_a_1120_, lean_object* v_b_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v___y_1129_; uint8_t v___x_1152_; 
v___x_1152_ = lean_nat_dec_lt(v_a_1120_, v_upperBound_1112_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; 
lean_dec(v_a_1120_);
lean_dec_ref(v_postApp_1119_);
lean_dec_ref(v_post_1115_);
lean_dec_ref(v_pre_1114_);
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v_b_1121_);
return v___x_1153_;
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1154_ = lean_array_fget_borrowed(v_b_1121_, v_a_1120_);
v___x_1155_ = lean_array_get_size(v___x_1113_);
v___x_1156_ = lean_nat_dec_lt(v_a_1120_, v___x_1155_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___f_1160_; 
lean_inc(v___x_1154_);
v___x_1157_ = lean_box(v_usedLetOnly_1116_);
v___x_1158_ = lean_box(v_skipConstInApp_1117_);
v___x_1159_ = lean_box(v_skipInstances_1118_);
lean_inc(v_a_1120_);
lean_inc(v___y_1122_);
lean_inc_ref(v_postApp_1119_);
lean_inc_ref(v_post_1115_);
lean_inc_ref(v_pre_1114_);
v___f_1160_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__0___boxed), 15, 10);
lean_closure_set(v___f_1160_, 0, v_pre_1114_);
lean_closure_set(v___f_1160_, 1, v_post_1115_);
lean_closure_set(v___f_1160_, 2, v___x_1157_);
lean_closure_set(v___f_1160_, 3, v___x_1158_);
lean_closure_set(v___f_1160_, 4, v___x_1159_);
lean_closure_set(v___f_1160_, 5, v_postApp_1119_);
lean_closure_set(v___f_1160_, 6, v___x_1154_);
lean_closure_set(v___f_1160_, 7, v___y_1122_);
lean_closure_set(v___f_1160_, 8, v_b_1121_);
lean_closure_set(v___f_1160_, 9, v_a_1120_);
v___y_1129_ = v___f_1160_;
goto v___jp_1128_;
}
else
{
lean_object* v___x_1161_; uint8_t v_isInstance_1162_; 
v___x_1161_ = lean_array_fget_borrowed(v___x_1113_, v_a_1120_);
v_isInstance_1162_ = lean_ctor_get_uint8(v___x_1161_, sizeof(void*)*1 + 4);
if (v_isInstance_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___f_1166_; 
lean_inc(v___x_1154_);
v___x_1163_ = lean_box(v_usedLetOnly_1116_);
v___x_1164_ = lean_box(v_skipConstInApp_1117_);
v___x_1165_ = lean_box(v_skipInstances_1118_);
lean_inc(v_a_1120_);
lean_inc(v___y_1122_);
lean_inc_ref(v_postApp_1119_);
lean_inc_ref(v_post_1115_);
lean_inc_ref(v_pre_1114_);
v___f_1166_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__0___boxed), 15, 10);
lean_closure_set(v___f_1166_, 0, v_pre_1114_);
lean_closure_set(v___f_1166_, 1, v_post_1115_);
lean_closure_set(v___f_1166_, 2, v___x_1163_);
lean_closure_set(v___f_1166_, 3, v___x_1164_);
lean_closure_set(v___f_1166_, 4, v___x_1165_);
lean_closure_set(v___f_1166_, 5, v_postApp_1119_);
lean_closure_set(v___f_1166_, 6, v___x_1154_);
lean_closure_set(v___f_1166_, 7, v___y_1122_);
lean_closure_set(v___f_1166_, 8, v_b_1121_);
lean_closure_set(v___f_1166_, 9, v_a_1120_);
v___y_1129_ = v___f_1166_;
goto v___jp_1128_;
}
else
{
lean_object* v___x_1167_; lean_object* v___f_1168_; 
v___x_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1167_, 0, v_b_1121_);
v___f_1168_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1168_, 0, v___x_1167_);
v___y_1129_ = v___f_1168_;
goto v___jp_1128_;
}
}
}
v___jp_1128_:
{
lean_object* v___x_1130_; 
lean_inc(v___y_1126_);
lean_inc_ref(v___y_1125_);
lean_inc(v___y_1124_);
lean_inc_ref(v___y_1123_);
v___x_1130_ = lean_apply_5(v___y_1129_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, lean_box(0));
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1143_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1133_ = v___x_1130_;
v_isShared_1134_ = v_isSharedCheck_1143_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1143_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
if (lean_obj_tag(v_a_1131_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1137_; 
lean_dec(v_a_1120_);
lean_dec_ref(v_postApp_1119_);
lean_dec_ref(v_post_1115_);
lean_dec_ref(v_pre_1114_);
v_a_1135_ = lean_ctor_get(v_a_1131_, 0);
lean_inc(v_a_1135_);
lean_dec_ref_known(v_a_1131_, 1);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v_a_1135_);
v___x_1137_ = v___x_1133_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
lean_del_object(v___x_1133_);
v_a_1139_ = lean_ctor_get(v_a_1131_, 0);
lean_inc(v_a_1139_);
lean_dec_ref_known(v_a_1131_, 1);
v___x_1140_ = lean_unsigned_to_nat(1u);
v___x_1141_ = lean_nat_add(v_a_1120_, v___x_1140_);
lean_dec(v_a_1120_);
v_a_1120_ = v___x_1141_;
v_b_1121_ = v_a_1139_;
goto _start;
}
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec(v_a_1120_);
lean_dec_ref(v_postApp_1119_);
lean_dec_ref(v_post_1115_);
lean_dec_ref(v_pre_1114_);
v_a_1144_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1130_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1130_);
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
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(uint8_t v_skipInstances_1169_, lean_object* v_pre_1170_, lean_object* v_post_1171_, uint8_t v_usedLetOnly_1172_, uint8_t v_skipConstInApp_1173_, lean_object* v_postApp_1174_, lean_object* v___y_1175_, lean_object* v_x_1176_, lean_object* v_x_1177_, lean_object* v_x_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_f_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; 
if (lean_obj_tag(v_x_1176_) == 5)
{
lean_object* v_fn_1238_; lean_object* v_arg_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v_fn_1238_ = lean_ctor_get(v_x_1176_, 0);
lean_inc_ref(v_fn_1238_);
v_arg_1239_ = lean_ctor_get(v_x_1176_, 1);
lean_inc_ref(v_arg_1239_);
lean_dec_ref_known(v_x_1176_, 2);
v___x_1240_ = lean_array_set(v_x_1177_, v_x_1178_, v_arg_1239_);
v___x_1241_ = lean_unsigned_to_nat(1u);
v___x_1242_ = lean_nat_sub(v_x_1178_, v___x_1241_);
lean_dec(v_x_1178_);
v_x_1176_ = v_fn_1238_;
v_x_1177_ = v___x_1240_;
v_x_1178_ = v___x_1242_;
goto _start;
}
else
{
lean_dec(v_x_1178_);
if (v_skipConstInApp_1173_ == 0)
{
goto v___jp_1235_;
}
else
{
uint8_t v___x_1244_; 
v___x_1244_ = l_Lean_Expr_isConst(v_x_1176_);
if (v___x_1244_ == 0)
{
goto v___jp_1235_;
}
else
{
v_f_1186_ = v_x_1176_;
v___y_1187_ = v___y_1179_;
v___y_1188_ = v___y_1180_;
v___y_1189_ = v___y_1181_;
v___y_1190_ = v___y_1182_;
v___y_1191_ = v___y_1183_;
goto v___jp_1185_;
}
}
}
v___jp_1185_:
{
if (v_skipInstances_1169_ == 0)
{
size_t v_sz_1192_; size_t v___x_1193_; lean_object* v___x_1194_; 
v_sz_1192_ = lean_array_size(v_x_1177_);
v___x_1193_ = ((size_t)0ULL);
lean_inc_ref(v_postApp_1174_);
lean_inc_ref(v_post_1171_);
lean_inc_ref(v_pre_1170_);
v___x_1194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1170_, v_post_1171_, v_usedLetOnly_1172_, v_skipConstInApp_1173_, v_skipInstances_1169_, v_postApp_1174_, v_sz_1192_, v___x_1193_, v_x_1177_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1194_, 1);
v___x_1196_ = l_Lean_mkAppN(v_f_1186_, v_a_1195_);
lean_dec(v_a_1195_);
lean_inc_ref(v_postApp_1174_);
lean_inc(v___y_1191_);
lean_inc_ref(v___y_1190_);
lean_inc(v___y_1189_);
lean_inc_ref(v___y_1188_);
v___x_1197_ = lean_apply_7(v_postApp_1174_, v___y_1175_, v___x_1196_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, lean_box(0));
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v___x_1199_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_a_1198_);
lean_dec_ref_known(v___x_1197_, 1);
v___x_1199_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_pre_1170_, v_post_1171_, v_usedLetOnly_1172_, v_skipConstInApp_1173_, v_skipInstances_1169_, v_postApp_1174_, v_a_1198_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
return v___x_1199_;
}
else
{
lean_dec_ref(v_postApp_1174_);
lean_dec_ref(v_post_1171_);
lean_dec_ref(v_pre_1170_);
return v___x_1197_;
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec_ref(v_f_1186_);
lean_dec_ref(v___y_1175_);
lean_dec_ref(v_postApp_1174_);
lean_dec_ref(v_post_1171_);
lean_dec_ref(v_pre_1170_);
v_a_1200_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1194_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1194_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = lean_array_get_size(v_x_1177_);
lean_inc_ref(v_f_1186_);
v___x_1209_ = l_Lean_Meta_getFunInfoNArgs(v_f_1186_, v___x_1208_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v_paramInfo_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
lean_dec_ref_known(v___x_1209_, 1);
v_paramInfo_1211_ = lean_ctor_get(v_a_1210_, 0);
lean_inc_ref(v_paramInfo_1211_);
lean_dec(v_a_1210_);
v___x_1212_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_postApp_1174_);
lean_inc_ref(v_post_1171_);
lean_inc_ref(v_pre_1170_);
v___x_1213_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v___x_1208_, v_paramInfo_1211_, v_pre_1170_, v_post_1171_, v_usedLetOnly_1172_, v_skipConstInApp_1173_, v_skipInstances_1169_, v_postApp_1174_, v___x_1212_, v_x_1177_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec_ref(v_paramInfo_1211_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1214_);
lean_dec_ref_known(v___x_1213_, 1);
v___x_1215_ = l_Lean_mkAppN(v_f_1186_, v_a_1214_);
lean_dec(v_a_1214_);
lean_inc_ref(v_postApp_1174_);
lean_inc(v___y_1191_);
lean_inc_ref(v___y_1190_);
lean_inc(v___y_1189_);
lean_inc_ref(v___y_1188_);
v___x_1216_ = lean_apply_7(v_postApp_1174_, v___y_1175_, v___x_1215_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, lean_box(0));
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1218_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1217_);
lean_dec_ref_known(v___x_1216_, 1);
v___x_1218_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_pre_1170_, v_post_1171_, v_usedLetOnly_1172_, v_skipConstInApp_1173_, v_skipInstances_1169_, v_postApp_1174_, v_a_1217_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
return v___x_1218_;
}
else
{
lean_dec_ref(v_postApp_1174_);
lean_dec_ref(v_post_1171_);
lean_dec_ref(v_pre_1170_);
return v___x_1216_;
}
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_dec_ref(v_f_1186_);
lean_dec_ref(v___y_1175_);
lean_dec_ref(v_postApp_1174_);
lean_dec_ref(v_post_1171_);
lean_dec_ref(v_pre_1170_);
v_a_1219_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1213_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1213_);
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
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_dec_ref(v_f_1186_);
lean_dec_ref(v_x_1177_);
lean_dec_ref(v___y_1175_);
lean_dec_ref(v_postApp_1174_);
lean_dec_ref(v_post_1171_);
lean_dec_ref(v_pre_1170_);
v_a_1227_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1209_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1209_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
v___jp_1235_:
{
lean_object* v___x_1236_; 
lean_inc_ref(v_postApp_1174_);
lean_inc_ref(v_post_1171_);
lean_inc_ref(v_pre_1170_);
v___x_1236_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1170_, v_post_1171_, v_usedLetOnly_1172_, v_skipConstInApp_1173_, v_skipInstances_1169_, v_postApp_1174_, v_x_1176_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1237_);
lean_dec_ref_known(v___x_1236_, 1);
v_f_1186_ = v_a_1237_;
v___y_1187_ = v___y_1179_;
v___y_1188_ = v___y_1180_;
v___y_1189_ = v___y_1181_;
v___y_1190_ = v___y_1182_;
v___y_1191_ = v___y_1183_;
goto v___jp_1185_;
}
else
{
lean_dec_ref(v_x_1177_);
lean_dec_ref(v___y_1175_);
lean_dec_ref(v_postApp_1174_);
lean_dec_ref(v_post_1171_);
lean_dec_ref(v_pre_1170_);
return v___x_1236_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(lean_object* v___x_1245_, lean_object* v_pre_1246_, lean_object* v_e_1247_, lean_object* v_post_1248_, uint8_t v_usedLetOnly_1249_, uint8_t v_skipConstInApp_1250_, uint8_t v_skipInstances_1251_, lean_object* v_postApp_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_Core_checkSystem(v___x_1245_, v___y_1256_, v___y_1257_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v___x_1260_; 
lean_dec_ref_known(v___x_1259_, 1);
lean_inc_ref(v_pre_1246_);
lean_inc(v___y_1257_);
lean_inc_ref(v___y_1256_);
lean_inc(v___y_1255_);
lean_inc_ref(v___y_1254_);
lean_inc_ref(v_e_1247_);
v___x_1260_ = lean_apply_6(v_pre_1246_, v_e_1247_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, lean_box(0));
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1309_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1309_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1309_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___y_1266_; 
switch(lean_obj_tag(v_a_1261_))
{
case 0:
{
lean_object* v_e_1301_; lean_object* v___x_1303_; 
lean_dec_ref(v_postApp_1252_);
lean_dec_ref(v_post_1248_);
lean_dec_ref(v_e_1247_);
lean_dec_ref(v_pre_1246_);
v_e_1301_ = lean_ctor_get(v_a_1261_, 0);
lean_inc_ref(v_e_1301_);
lean_dec_ref_known(v_a_1261_, 1);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v_e_1301_);
v___x_1303_ = v___x_1263_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_e_1301_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
case 1:
{
lean_object* v_e_1305_; lean_object* v___x_1306_; 
lean_del_object(v___x_1263_);
lean_dec_ref(v_e_1247_);
v_e_1305_ = lean_ctor_get(v_a_1261_, 0);
lean_inc_ref(v_e_1305_);
lean_dec_ref_known(v_a_1261_, 1);
v___x_1306_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1246_, v_post_1248_, v_usedLetOnly_1249_, v_skipConstInApp_1250_, v_skipInstances_1251_, v_postApp_1252_, v_e_1305_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v___x_1306_;
}
default: 
{
lean_object* v_e_x3f_1307_; 
lean_del_object(v___x_1263_);
v_e_x3f_1307_ = lean_ctor_get(v_a_1261_, 0);
lean_inc(v_e_x3f_1307_);
lean_dec_ref_known(v_a_1261_, 1);
if (lean_obj_tag(v_e_x3f_1307_) == 0)
{
v___y_1266_ = v_e_1247_;
goto v___jp_1265_;
}
else
{
lean_object* v_val_1308_; 
lean_dec_ref(v_e_1247_);
v_val_1308_ = lean_ctor_get(v_e_x3f_1307_, 0);
lean_inc(v_val_1308_);
lean_dec_ref_known(v_e_x3f_1307_, 1);
v___y_1266_ = v_val_1308_;
goto v___jp_1265_;
}
}
}
v___jp_1265_:
{
switch(lean_obj_tag(v___y_1266_))
{
case 7:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1268_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1246_, v_post_1248_, v_usedLetOnly_1249_, v_skipConstInApp_1250_, v_skipInstances_1251_, v_postApp_1252_, v___x_1267_, v___y_1266_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v___x_1268_;
}
case 6:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1270_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_1246_, v_post_1248_, v_usedLetOnly_1249_, v_skipConstInApp_1250_, v_skipInstances_1251_, v_postApp_1252_, v___x_1269_, v___y_1266_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v___x_1270_;
}
case 8:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1272_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_1246_, v_post_1248_, v_usedLetOnly_1249_, v_skipConstInApp_1250_, v_skipInstances_1251_, v_postApp_1252_, v___x_1271_, v___y_1266_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v___x_1272_;
}
case 5:
{
lean_object* v_dummy_1273_; lean_object* v_nargs_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v_dummy_1273_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1);
v_nargs_1274_ = l_Lean_Expr_getAppNumArgs(v___y_1266_);
lean_inc(v_nargs_1274_);
v___x_1275_ = lean_mk_array(v_nargs_1274_, v_dummy_1273_);
v___x_1276_ = lean_unsigned_to_nat(1u);
v___x_1277_ = lean_nat_sub(v_nargs_1274_, v___x_1276_);
lean_dec(v_nargs_1274_);
lean_inc_ref(v___y_1266_);
v___x_1278_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_1251_, v_pre_1246_, v_post_1248_, v_usedLetOnly_1249_, v_skipConstInApp_1250_, v_postApp_1252_, v___y_1266_, v___y_1266_, v___x_1275_, v___x_1277_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v___x_1278_;
}
case 10:
{
lean_object* v_data_1279_; lean_object* v_expr_1280_; lean_object* v___x_1281_; 
v_data_1279_ = lean_ctor_get(v___y_1266_, 0);
v_expr_1280_ = lean_ctor_get(v___y_1266_, 1);
lean_inc_ref(v_expr_1280_);
lean_inc_ref(v_postApp_1252_);
lean_inc_ref(v_post_1248_);
lean_inc_ref(v_pre_1246_);
v___x_1281_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1246_, v_post_1248_, v_usedLetOnly_1249_, v_skipConstInApp_1250_, v_skipInstances_1251_, v_postApp_1252_, v_expr_1280_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; size_t v___x_1283_; size_t v___x_1284_; uint8_t v___x_1285_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1282_);
lean_dec_ref_known(v___x_1281_, 1);
v___x_1283_ = lean_ptr_addr(v_expr_1280_);
v___x_1284_ = lean_ptr_addr(v_a_1282_);
v___x_1285_ = lean_usize_dec_eq(v___x_1283_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
lean_inc(v_data_1279_);
lean_dec_ref_known(v___y_1266_, 2);
v___x_1286_ = l_Lean_Expr_mdata___override(v_data_1279_, v_a_1282_);
v___x_1287_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_pre_1246_, v_post_1248_, v_usedLetOnly_1249_, v_skipConstInApp_1250_, v_skipInstances_1251_, v_postApp_1252_, v___x_1286_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v___x_1287_;
}
else
{
lean_object* v___x_1288_; 
lean_dec(v_a_1282_);
v___x_1288_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_pre_1246_, v_post_1248_, v_usedLetOnly_1249_, v_skipConstInApp_1250_, v_skipInstances_1251_, v_postApp_1252_, v___y_1266_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v___x_1288_;
}
}
else
{
lean_dec_ref_known(v___y_1266_, 2);
lean_dec_ref(v_postApp_1252_);
lean_dec_ref(v_post_1248_);
lean_dec_ref(v_pre_1246_);
return v___x_1281_;
}
}
case 11:
{
lean_object* v_typeName_1289_; lean_object* v_idx_1290_; lean_object* v_struct_1291_; lean_object* v___x_1292_; 
v_typeName_1289_ = lean_ctor_get(v___y_1266_, 0);
v_idx_1290_ = lean_ctor_get(v___y_1266_, 1);
v_struct_1291_ = lean_ctor_get(v___y_1266_, 2);
lean_inc_ref(v_struct_1291_);
lean_inc_ref(v_postApp_1252_);
lean_inc_ref(v_post_1248_);
lean_inc_ref(v_pre_1246_);
v___x_1292_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1246_, v_post_1248_, v_usedLetOnly_1249_, v_skipConstInApp_1250_, v_skipInstances_1251_, v_postApp_1252_, v_struct_1291_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; size_t v___x_1294_; size_t v___x_1295_; uint8_t v___x_1296_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1293_);
lean_dec_ref_known(v___x_1292_, 1);
v___x_1294_ = lean_ptr_addr(v_struct_1291_);
v___x_1295_ = lean_ptr_addr(v_a_1293_);
v___x_1296_ = lean_usize_dec_eq(v___x_1294_, v___x_1295_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
lean_inc(v_idx_1290_);
lean_inc(v_typeName_1289_);
lean_dec_ref_known(v___y_1266_, 3);
v___x_1297_ = l_Lean_Expr_proj___override(v_typeName_1289_, v_idx_1290_, v_a_1293_);
v___x_1298_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_pre_1246_, v_post_1248_, v_usedLetOnly_1249_, v_skipConstInApp_1250_, v_skipInstances_1251_, v_postApp_1252_, v___x_1297_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v___x_1298_;
}
else
{
lean_object* v___x_1299_; 
lean_dec(v_a_1293_);
v___x_1299_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_pre_1246_, v_post_1248_, v_usedLetOnly_1249_, v_skipConstInApp_1250_, v_skipInstances_1251_, v_postApp_1252_, v___y_1266_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v___x_1299_;
}
}
else
{
lean_dec_ref_known(v___y_1266_, 3);
lean_dec_ref(v_postApp_1252_);
lean_dec_ref(v_post_1248_);
lean_dec_ref(v_pre_1246_);
return v___x_1292_;
}
}
default: 
{
lean_object* v___x_1300_; 
v___x_1300_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_pre_1246_, v_post_1248_, v_usedLetOnly_1249_, v_skipConstInApp_1250_, v_skipInstances_1251_, v_postApp_1252_, v___y_1266_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v___x_1300_;
}
}
}
}
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
lean_dec_ref(v_postApp_1252_);
lean_dec_ref(v_post_1248_);
lean_dec_ref(v_e_1247_);
lean_dec_ref(v_pre_1246_);
v_a_1310_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1260_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1260_);
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
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
lean_dec_ref(v_postApp_1252_);
lean_dec_ref(v_post_1248_);
lean_dec_ref(v_e_1247_);
lean_dec_ref(v_pre_1246_);
v_a_1318_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1259_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1259_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1326_, lean_object* v_pre_1327_, lean_object* v_e_1328_, lean_object* v_post_1329_, lean_object* v_usedLetOnly_1330_, lean_object* v_skipConstInApp_1331_, lean_object* v_skipInstances_1332_, lean_object* v_postApp_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
uint8_t v_usedLetOnly_boxed_1340_; uint8_t v_skipConstInApp_boxed_1341_; uint8_t v_skipInstances_boxed_1342_; lean_object* v_res_1343_; 
v_usedLetOnly_boxed_1340_ = lean_unbox(v_usedLetOnly_1330_);
v_skipConstInApp_boxed_1341_ = lean_unbox(v_skipConstInApp_1331_);
v_skipInstances_boxed_1342_ = lean_unbox(v_skipInstances_1332_);
v_res_1343_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(v___x_1326_, v_pre_1327_, v_e_1328_, v_post_1329_, v_usedLetOnly_boxed_1340_, v_skipConstInApp_boxed_1341_, v_skipInstances_boxed_1342_, v_postApp_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(lean_object* v_pre_1344_, lean_object* v_post_1345_, uint8_t v_usedLetOnly_1346_, uint8_t v_skipConstInApp_1347_, uint8_t v_skipInstances_1348_, lean_object* v_postApp_1349_, lean_object* v_e_1350_, lean_object* v_a_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_inc(v_a_1351_);
v___x_1357_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1357_, 0, lean_box(0));
lean_closure_set(v___x_1357_, 1, lean_box(0));
lean_closure_set(v___x_1357_, 2, v_a_1351_);
v___x_1358_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v___x_1357_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1393_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1361_ = v___x_1358_;
v_isShared_1362_ = v_isSharedCheck_1393_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1358_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1393_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___redArg(v_a_1359_, v_e_1350_);
lean_dec(v_a_1359_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___f_1368_; lean_object* v___x_1369_; 
lean_del_object(v___x_1361_);
v___x_1364_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0));
v___x_1365_ = lean_box(v_usedLetOnly_1346_);
v___x_1366_ = lean_box(v_skipConstInApp_1347_);
v___x_1367_ = lean_box(v_skipInstances_1348_);
lean_inc_ref(v_e_1350_);
v___f_1368_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed), 14, 8);
lean_closure_set(v___f_1368_, 0, v___x_1364_);
lean_closure_set(v___f_1368_, 1, v_pre_1344_);
lean_closure_set(v___f_1368_, 2, v_e_1350_);
lean_closure_set(v___f_1368_, 3, v_post_1345_);
lean_closure_set(v___f_1368_, 4, v___x_1365_);
lean_closure_set(v___f_1368_, 5, v___x_1366_);
lean_closure_set(v___f_1368_, 6, v___x_1367_);
lean_closure_set(v___f_1368_, 7, v_postApp_1349_);
v___x_1369_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v___f_1368_, v_a_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v___f_1371_; lean_object* v___x_1372_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc_n(v_a_1370_, 2);
lean_dec_ref_known(v___x_1369_, 1);
lean_inc(v_a_1351_);
v___f_1371_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1371_, 0, v_a_1351_);
lean_closure_set(v___f_1371_, 1, v_e_1350_);
lean_closure_set(v___f_1371_, 2, v_a_1370_);
v___x_1372_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v___f_1371_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1379_ == 0)
{
lean_object* v_unused_1380_; 
v_unused_1380_ = lean_ctor_get(v___x_1372_, 0);
lean_dec(v_unused_1380_);
v___x_1374_ = v___x_1372_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_dec(v___x_1372_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 0, v_a_1370_);
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1370_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec(v_a_1370_);
v_a_1381_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1372_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1372_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
else
{
lean_dec_ref(v_e_1350_);
return v___x_1369_;
}
}
else
{
lean_object* v_val_1389_; lean_object* v___x_1391_; 
lean_dec_ref(v_e_1350_);
lean_dec_ref(v_postApp_1349_);
lean_dec_ref(v_post_1345_);
lean_dec_ref(v_pre_1344_);
v_val_1389_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_val_1389_);
lean_dec_ref_known(v___x_1363_, 1);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v_val_1389_);
v___x_1391_ = v___x_1361_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_val_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_dec_ref(v_e_1350_);
lean_dec_ref(v_postApp_1349_);
lean_dec_ref(v_post_1345_);
lean_dec_ref(v_pre_1344_);
v_a_1394_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1358_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1358_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(lean_object* v_pre_1402_, lean_object* v_post_1403_, uint8_t v_usedLetOnly_1404_, uint8_t v_skipConstInApp_1405_, uint8_t v_skipInstances_1406_, lean_object* v_postApp_1407_, lean_object* v_fvars_1408_, lean_object* v_e_1409_, lean_object* v_a_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
if (lean_obj_tag(v_e_1409_) == 7)
{
lean_object* v_binderName_1416_; lean_object* v_binderType_1417_; lean_object* v_body_1418_; uint8_t v_binderInfo_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___f_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v_binderName_1416_ = lean_ctor_get(v_e_1409_, 0);
lean_inc(v_binderName_1416_);
v_binderType_1417_ = lean_ctor_get(v_e_1409_, 1);
lean_inc_ref(v_binderType_1417_);
v_body_1418_ = lean_ctor_get(v_e_1409_, 2);
lean_inc_ref(v_body_1418_);
v_binderInfo_1419_ = lean_ctor_get_uint8(v_e_1409_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1409_, 3);
v___x_1420_ = lean_box(v_usedLetOnly_1404_);
v___x_1421_ = lean_box(v_skipConstInApp_1405_);
v___x_1422_ = lean_box(v_skipInstances_1406_);
lean_inc_ref(v_postApp_1407_);
lean_inc_ref(v_post_1403_);
lean_inc_ref(v_pre_1402_);
lean_inc_ref(v_fvars_1408_);
v___f_1423_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed), 15, 8);
lean_closure_set(v___f_1423_, 0, v_fvars_1408_);
lean_closure_set(v___f_1423_, 1, v_pre_1402_);
lean_closure_set(v___f_1423_, 2, v_post_1403_);
lean_closure_set(v___f_1423_, 3, v___x_1420_);
lean_closure_set(v___f_1423_, 4, v___x_1421_);
lean_closure_set(v___f_1423_, 5, v___x_1422_);
lean_closure_set(v___f_1423_, 6, v_postApp_1407_);
lean_closure_set(v___f_1423_, 7, v_body_1418_);
v___x_1424_ = lean_expr_instantiate_rev(v_binderType_1417_, v_fvars_1408_);
lean_dec_ref(v_fvars_1408_);
lean_dec_ref(v_binderType_1417_);
v___x_1425_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1402_, v_post_1403_, v_usedLetOnly_1404_, v_skipConstInApp_1405_, v_skipInstances_1406_, v_postApp_1407_, v___x_1424_, v_a_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; uint8_t v___x_1427_; lean_object* v___x_1428_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
lean_dec_ref_known(v___x_1425_, 1);
v___x_1427_ = 0;
v___x_1428_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_1416_, v_binderInfo_1419_, v_a_1426_, v___f_1423_, v___x_1427_, v_a_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
return v___x_1428_;
}
else
{
lean_dec_ref(v___f_1423_);
lean_dec(v_binderName_1416_);
return v___x_1425_;
}
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = lean_expr_instantiate_rev(v_e_1409_, v_fvars_1408_);
lean_dec_ref(v_e_1409_);
lean_inc_ref(v_postApp_1407_);
lean_inc_ref(v_post_1403_);
lean_inc_ref(v_pre_1402_);
v___x_1430_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1402_, v_post_1403_, v_usedLetOnly_1404_, v_skipConstInApp_1405_, v_skipInstances_1406_, v_postApp_1407_, v___x_1429_, v_a_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; uint8_t v___x_1432_; uint8_t v___x_1433_; uint8_t v___x_1434_; lean_object* v___x_1435_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v___x_1432_ = 0;
v___x_1433_ = 1;
v___x_1434_ = 1;
v___x_1435_ = l_Lean_Meta_mkForallFVars(v_fvars_1408_, v_a_1431_, v___x_1432_, v_usedLetOnly_1404_, v___x_1433_, v___x_1434_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec_ref(v_fvars_1408_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1437_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_a_1436_);
lean_dec_ref_known(v___x_1435_, 1);
v___x_1437_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_pre_1402_, v_post_1403_, v_usedLetOnly_1404_, v_skipConstInApp_1405_, v_skipInstances_1406_, v_postApp_1407_, v_a_1436_, v_a_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
return v___x_1437_;
}
else
{
lean_dec_ref(v_postApp_1407_);
lean_dec_ref(v_post_1403_);
lean_dec_ref(v_pre_1402_);
return v___x_1435_;
}
}
else
{
lean_dec_ref(v_fvars_1408_);
lean_dec_ref(v_postApp_1407_);
lean_dec_ref(v_post_1403_);
lean_dec_ref(v_pre_1402_);
return v___x_1430_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(lean_object* v_fvars_1438_, lean_object* v_pre_1439_, lean_object* v_post_1440_, uint8_t v_usedLetOnly_1441_, uint8_t v_skipConstInApp_1442_, uint8_t v_skipInstances_1443_, lean_object* v_postApp_1444_, lean_object* v_body_1445_, lean_object* v_x_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = lean_array_push(v_fvars_1438_, v_x_1446_);
v___x_1454_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1439_, v_post_1440_, v_usedLetOnly_1441_, v_skipConstInApp_1442_, v_skipInstances_1443_, v_postApp_1444_, v___x_1453_, v_body_1445_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___boxed(lean_object* v_pre_1455_, lean_object* v_post_1456_, lean_object* v_usedLetOnly_1457_, lean_object* v_skipConstInApp_1458_, lean_object* v_skipInstances_1459_, lean_object* v_postApp_1460_, lean_object* v_e_1461_, lean_object* v_a_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
uint8_t v_usedLetOnly_boxed_1468_; uint8_t v_skipConstInApp_boxed_1469_; uint8_t v_skipInstances_boxed_1470_; lean_object* v_res_1471_; 
v_usedLetOnly_boxed_1468_ = lean_unbox(v_usedLetOnly_1457_);
v_skipConstInApp_boxed_1469_ = lean_unbox(v_skipConstInApp_1458_);
v_skipInstances_boxed_1470_ = lean_unbox(v_skipInstances_1459_);
v_res_1471_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_pre_1455_, v_post_1456_, v_usedLetOnly_boxed_1468_, v_skipConstInApp_boxed_1469_, v_skipInstances_boxed_1470_, v_postApp_1460_, v_e_1461_, v_a_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v_a_1462_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1472_, lean_object* v_post_1473_, lean_object* v_usedLetOnly_1474_, lean_object* v_skipConstInApp_1475_, lean_object* v_skipInstances_1476_, lean_object* v_postApp_1477_, lean_object* v_sz_1478_, lean_object* v_i_1479_, lean_object* v_bs_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
uint8_t v_usedLetOnly_boxed_1487_; uint8_t v_skipConstInApp_boxed_1488_; uint8_t v_skipInstances_boxed_1489_; size_t v_sz_boxed_1490_; size_t v_i_boxed_1491_; lean_object* v_res_1492_; 
v_usedLetOnly_boxed_1487_ = lean_unbox(v_usedLetOnly_1474_);
v_skipConstInApp_boxed_1488_ = lean_unbox(v_skipConstInApp_1475_);
v_skipInstances_boxed_1489_ = lean_unbox(v_skipInstances_1476_);
v_sz_boxed_1490_ = lean_unbox_usize(v_sz_1478_);
lean_dec(v_sz_1478_);
v_i_boxed_1491_ = lean_unbox_usize(v_i_1479_);
lean_dec(v_i_1479_);
v_res_1492_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1472_, v_post_1473_, v_usedLetOnly_boxed_1487_, v_skipConstInApp_boxed_1488_, v_skipInstances_boxed_1489_, v_postApp_1477_, v_sz_boxed_1490_, v_i_boxed_1491_, v_bs_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___boxed(lean_object* v_pre_1493_, lean_object* v_post_1494_, lean_object* v_usedLetOnly_1495_, lean_object* v_skipConstInApp_1496_, lean_object* v_skipInstances_1497_, lean_object* v_postApp_1498_, lean_object* v_e_1499_, lean_object* v_a_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
uint8_t v_usedLetOnly_boxed_1506_; uint8_t v_skipConstInApp_boxed_1507_; uint8_t v_skipInstances_boxed_1508_; lean_object* v_res_1509_; 
v_usedLetOnly_boxed_1506_ = lean_unbox(v_usedLetOnly_1495_);
v_skipConstInApp_boxed_1507_ = lean_unbox(v_skipConstInApp_1496_);
v_skipInstances_boxed_1508_ = lean_unbox(v_skipInstances_1497_);
v_res_1509_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1493_, v_post_1494_, v_usedLetOnly_boxed_1506_, v_skipConstInApp_boxed_1507_, v_skipInstances_boxed_1508_, v_postApp_1498_, v_e_1499_, v_a_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v_a_1500_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___boxed(lean_object* v_pre_1510_, lean_object* v_post_1511_, lean_object* v_usedLetOnly_1512_, lean_object* v_skipConstInApp_1513_, lean_object* v_skipInstances_1514_, lean_object* v_postApp_1515_, lean_object* v_fvars_1516_, lean_object* v_e_1517_, lean_object* v_a_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
uint8_t v_usedLetOnly_boxed_1524_; uint8_t v_skipConstInApp_boxed_1525_; uint8_t v_skipInstances_boxed_1526_; lean_object* v_res_1527_; 
v_usedLetOnly_boxed_1524_ = lean_unbox(v_usedLetOnly_1512_);
v_skipConstInApp_boxed_1525_ = lean_unbox(v_skipConstInApp_1513_);
v_skipInstances_boxed_1526_ = lean_unbox(v_skipInstances_1514_);
v_res_1527_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1510_, v_post_1511_, v_usedLetOnly_boxed_1524_, v_skipConstInApp_boxed_1525_, v_skipInstances_boxed_1526_, v_postApp_1515_, v_fvars_1516_, v_e_1517_, v_a_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v_a_1518_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___boxed(lean_object* v_pre_1528_, lean_object* v_post_1529_, lean_object* v_usedLetOnly_1530_, lean_object* v_skipConstInApp_1531_, lean_object* v_skipInstances_1532_, lean_object* v_postApp_1533_, lean_object* v_fvars_1534_, lean_object* v_e_1535_, lean_object* v_a_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
uint8_t v_usedLetOnly_boxed_1542_; uint8_t v_skipConstInApp_boxed_1543_; uint8_t v_skipInstances_boxed_1544_; lean_object* v_res_1545_; 
v_usedLetOnly_boxed_1542_ = lean_unbox(v_usedLetOnly_1530_);
v_skipConstInApp_boxed_1543_ = lean_unbox(v_skipConstInApp_1531_);
v_skipInstances_boxed_1544_ = lean_unbox(v_skipInstances_1532_);
v_res_1545_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_1528_, v_post_1529_, v_usedLetOnly_boxed_1542_, v_skipConstInApp_boxed_1543_, v_skipInstances_boxed_1544_, v_postApp_1533_, v_fvars_1534_, v_e_1535_, v_a_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v_a_1536_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___boxed(lean_object* v_pre_1546_, lean_object* v_post_1547_, lean_object* v_usedLetOnly_1548_, lean_object* v_skipConstInApp_1549_, lean_object* v_skipInstances_1550_, lean_object* v_postApp_1551_, lean_object* v_fvars_1552_, lean_object* v_e_1553_, lean_object* v_a_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
uint8_t v_usedLetOnly_boxed_1560_; uint8_t v_skipConstInApp_boxed_1561_; uint8_t v_skipInstances_boxed_1562_; lean_object* v_res_1563_; 
v_usedLetOnly_boxed_1560_ = lean_unbox(v_usedLetOnly_1548_);
v_skipConstInApp_boxed_1561_ = lean_unbox(v_skipConstInApp_1549_);
v_skipInstances_boxed_1562_ = lean_unbox(v_skipInstances_1550_);
v_res_1563_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_1546_, v_post_1547_, v_usedLetOnly_boxed_1560_, v_skipConstInApp_boxed_1561_, v_skipInstances_boxed_1562_, v_postApp_1551_, v_fvars_1552_, v_e_1553_, v_a_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v_a_1554_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_upperBound_1564_, lean_object* v___x_1565_, lean_object* v_pre_1566_, lean_object* v_post_1567_, lean_object* v_usedLetOnly_1568_, lean_object* v_skipConstInApp_1569_, lean_object* v_skipInstances_1570_, lean_object* v_postApp_1571_, lean_object* v_a_1572_, lean_object* v_b_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
uint8_t v_usedLetOnly_boxed_1580_; uint8_t v_skipConstInApp_boxed_1581_; uint8_t v_skipInstances_boxed_1582_; lean_object* v_res_1583_; 
v_usedLetOnly_boxed_1580_ = lean_unbox(v_usedLetOnly_1568_);
v_skipConstInApp_boxed_1581_ = lean_unbox(v_skipConstInApp_1569_);
v_skipInstances_boxed_1582_ = lean_unbox(v_skipInstances_1570_);
v_res_1583_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_upperBound_1564_, v___x_1565_, v_pre_1566_, v_post_1567_, v_usedLetOnly_boxed_1580_, v_skipConstInApp_boxed_1581_, v_skipInstances_boxed_1582_, v_postApp_1571_, v_a_1572_, v_b_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec_ref(v___x_1565_);
lean_dec(v_upperBound_1564_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8___boxed(lean_object* v_skipInstances_1584_, lean_object* v_pre_1585_, lean_object* v_post_1586_, lean_object* v_usedLetOnly_1587_, lean_object* v_skipConstInApp_1588_, lean_object* v_postApp_1589_, lean_object* v___y_1590_, lean_object* v_x_1591_, lean_object* v_x_1592_, lean_object* v_x_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
uint8_t v_skipInstances_boxed_1600_; uint8_t v_usedLetOnly_boxed_1601_; uint8_t v_skipConstInApp_boxed_1602_; lean_object* v_res_1603_; 
v_skipInstances_boxed_1600_ = lean_unbox(v_skipInstances_1584_);
v_usedLetOnly_boxed_1601_ = lean_unbox(v_usedLetOnly_1587_);
v_skipConstInApp_boxed_1602_ = lean_unbox(v_skipConstInApp_1588_);
v_res_1603_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_boxed_1600_, v_pre_1585_, v_post_1586_, v_usedLetOnly_boxed_1601_, v_skipConstInApp_boxed_1602_, v_postApp_1589_, v___y_1590_, v_x_1591_, v_x_1592_, v_x_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
return v_res_1603_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1605_ = lean_box(0);
v___x_1606_ = lean_unsigned_to_nat(16u);
v___x_1607_ = lean_mk_array(v___x_1606_, v___x_1605_);
return v___x_1607_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1608_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_1609_ = lean_unsigned_to_nat(0u);
v___x_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v___x_1608_);
return v___x_1610_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
v___x_1612_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1612_, 0, lean_box(0));
lean_closure_set(v___x_1612_, 1, lean_box(0));
lean_closure_set(v___x_1612_, 2, v___x_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(lean_object* v_input_1613_, lean_object* v_pre_1614_, lean_object* v_post_1615_, uint8_t v_usedLetOnly_1616_, uint8_t v_skipConstInApp_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v___f_1623_; uint8_t v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v_a_1627_; lean_object* v___x_1628_; 
v___f_1623_ = ((lean_object*)(l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0));
v___x_1624_ = 0;
v___x_1625_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__3, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__3_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__3);
v___x_1626_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v___x_1625_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref(v___x_1626_);
v___x_1628_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1614_, v_post_1615_, v_usedLetOnly_1616_, v_skipConstInApp_1617_, v___x_1624_, v___f_1623_, v_input_1613_, v_a_1627_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1629_);
lean_dec_ref_known(v___x_1628_, 1);
v___x_1630_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1630_, 0, lean_box(0));
lean_closure_set(v___x_1630_, 1, lean_box(0));
lean_closure_set(v___x_1630_, 2, v_a_1627_);
v___x_1631_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v___x_1630_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1638_ == 0)
{
lean_object* v_unused_1639_; 
v_unused_1639_ = lean_ctor_get(v___x_1631_, 0);
lean_dec(v_unused_1639_);
v___x_1633_ = v___x_1631_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_dec(v___x_1631_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v_a_1629_);
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1629_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
else
{
lean_dec(v_a_1627_);
return v___x_1628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___boxed(lean_object* v_input_1640_, lean_object* v_pre_1641_, lean_object* v_post_1642_, lean_object* v_usedLetOnly_1643_, lean_object* v_skipConstInApp_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
uint8_t v_usedLetOnly_boxed_1650_; uint8_t v_skipConstInApp_boxed_1651_; lean_object* v_res_1652_; 
v_usedLetOnly_boxed_1650_ = lean_unbox(v_usedLetOnly_1643_);
v_skipConstInApp_boxed_1651_ = lean_unbox(v_skipConstInApp_1644_);
v_res_1652_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_input_1640_, v_pre_1641_, v_post_1642_, v_usedLetOnly_boxed_1650_, v_skipConstInApp_boxed_1651_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object* v_e_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v___f_1661_; lean_object* v___x_1662_; lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1674_; 
v___f_1661_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducible___closed__0));
v___x_1662_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_1655_, v_a_1659_);
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1665_ = v___x_1662_;
v_isShared_1666_ = v_isSharedCheck_1674_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1662_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1674_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
uint8_t v___x_1667_; 
v___x_1667_ = lean_unbox(v_a_1663_);
lean_dec(v_a_1663_);
if (v___x_1667_ == 0)
{
lean_object* v___x_1669_; 
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v_e_1655_);
v___x_1669_ = v___x_1665_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_e_1655_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
else
{
uint8_t v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
lean_del_object(v___x_1665_);
v___x_1671_ = 0;
v___x_1672_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducible___closed__1));
v___x_1673_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_e_1655_, v___x_1672_, v___f_1661_, v___x_1671_, v___x_1671_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_);
return v___x_1673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___boxed(lean_object* v_e_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lean_Meta_Sym_unfoldReducible(v_e_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec(v_a_1677_);
lean_dec_ref(v_a_1676_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1682_, lean_object* v_m_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___redArg(v_m_1683_, v_a_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1686_, lean_object* v_m_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_00_u03b2_1686_, v_m_1687_, v_a_1688_);
lean_dec_ref(v_a_1688_);
lean_dec_ref(v_m_1687_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(lean_object* v_upperBound_1690_, lean_object* v___x_1691_, lean_object* v_pre_1692_, lean_object* v_post_1693_, uint8_t v_usedLetOnly_1694_, uint8_t v_skipConstInApp_1695_, uint8_t v_skipInstances_1696_, lean_object* v_postApp_1697_, lean_object* v___x_1698_, lean_object* v_inst_1699_, lean_object* v_R_1700_, lean_object* v_a_1701_, lean_object* v_b_1702_, lean_object* v_c_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_upperBound_1690_, v___x_1691_, v_pre_1692_, v_post_1693_, v_usedLetOnly_1694_, v_skipConstInApp_1695_, v_skipInstances_1696_, v_postApp_1697_, v_a_1701_, v_b_1702_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_1711_ = _args[0];
lean_object* v___x_1712_ = _args[1];
lean_object* v_pre_1713_ = _args[2];
lean_object* v_post_1714_ = _args[3];
lean_object* v_usedLetOnly_1715_ = _args[4];
lean_object* v_skipConstInApp_1716_ = _args[5];
lean_object* v_skipInstances_1717_ = _args[6];
lean_object* v_postApp_1718_ = _args[7];
lean_object* v___x_1719_ = _args[8];
lean_object* v_inst_1720_ = _args[9];
lean_object* v_R_1721_ = _args[10];
lean_object* v_a_1722_ = _args[11];
lean_object* v_b_1723_ = _args[12];
lean_object* v_c_1724_ = _args[13];
lean_object* v___y_1725_ = _args[14];
lean_object* v___y_1726_ = _args[15];
lean_object* v___y_1727_ = _args[16];
lean_object* v___y_1728_ = _args[17];
lean_object* v___y_1729_ = _args[18];
lean_object* v___y_1730_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_1731_; uint8_t v_skipConstInApp_boxed_1732_; uint8_t v_skipInstances_boxed_1733_; lean_object* v_res_1734_; 
v_usedLetOnly_boxed_1731_ = lean_unbox(v_usedLetOnly_1715_);
v_skipConstInApp_boxed_1732_ = lean_unbox(v_skipConstInApp_1716_);
v_skipInstances_boxed_1733_ = lean_unbox(v_skipInstances_1717_);
v_res_1734_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(v_upperBound_1711_, v___x_1712_, v_pre_1713_, v_post_1714_, v_usedLetOnly_boxed_1731_, v_skipConstInApp_boxed_1732_, v_skipInstances_boxed_1733_, v_postApp_1718_, v___x_1719_, v_inst_1720_, v_R_1721_, v_a_1722_, v_b_1723_, v_c_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec(v___x_1719_);
lean_dec_ref(v___x_1712_);
lean_dec(v_upperBound_1711_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1735_, lean_object* v_name_1736_, uint8_t v_bi_1737_, lean_object* v_type_1738_, lean_object* v_k_1739_, uint8_t v_kind_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_1736_, v_bi_1737_, v_type_1738_, v_k_1739_, v_kind_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1748_, lean_object* v_name_1749_, lean_object* v_bi_1750_, lean_object* v_type_1751_, lean_object* v_k_1752_, lean_object* v_kind_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
uint8_t v_bi_boxed_1760_; uint8_t v_kind_boxed_1761_; lean_object* v_res_1762_; 
v_bi_boxed_1760_ = lean_unbox(v_bi_1750_);
v_kind_boxed_1761_ = lean_unbox(v_kind_1753_);
v_res_1762_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1748_, v_name_1749_, v_bi_boxed_1760_, v_type_1751_, v_k_1752_, v_kind_boxed_1761_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(lean_object* v_00_u03b1_1763_, lean_object* v_name_1764_, lean_object* v_type_1765_, lean_object* v_val_1766_, lean_object* v_k_1767_, uint8_t v_nondep_1768_, uint8_t v_kind_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_1764_, v_type_1765_, v_val_1766_, v_k_1767_, v_nondep_1768_, v_kind_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1777_, lean_object* v_name_1778_, lean_object* v_type_1779_, lean_object* v_val_1780_, lean_object* v_k_1781_, lean_object* v_nondep_1782_, lean_object* v_kind_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
uint8_t v_nondep_boxed_1790_; uint8_t v_kind_boxed_1791_; lean_object* v_res_1792_; 
v_nondep_boxed_1790_ = lean_unbox(v_nondep_1782_);
v_kind_boxed_1791_ = lean_unbox(v_kind_1783_);
v_res_1792_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_1777_, v_name_1778_, v_type_1779_, v_val_1780_, v_k_1781_, v_nondep_boxed_1790_, v_kind_boxed_1791_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(lean_object* v_00_u03b1_1793_, lean_object* v_ref_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1794_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___boxed(lean_object* v_00_u03b1_1801_, lean_object* v_ref_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_1801_, v_ref_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(lean_object* v_00_u03b1_1809_, lean_object* v_x_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___boxed(lean_object* v_00_u03b1_1818_, lean_object* v_x_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(v_00_u03b1_1818_, v_x_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10(lean_object* v_00_u03b2_1827_, lean_object* v_m_1828_, lean_object* v_a_1829_, lean_object* v_b_1830_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v_m_1828_, v_a_1829_, v_b_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1832_, lean_object* v_a_1833_, lean_object* v_x_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_spec__2___redArg(v_a_1833_, v_x_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1836_, lean_object* v_a_1837_, lean_object* v_x_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_1836_, v_a_1837_, v_x_1838_);
lean_dec(v_x_1838_);
lean_dec_ref(v_a_1837_);
return v_res_1839_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(lean_object* v_00_u03b2_1840_, lean_object* v_a_1841_, lean_object* v_x_1842_){
_start:
{
uint8_t v___x_1843_; 
v___x_1843_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_1841_, v_x_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___boxed(lean_object* v_00_u03b2_1844_, lean_object* v_a_1845_, lean_object* v_x_1846_){
_start:
{
uint8_t v_res_1847_; lean_object* v_r_1848_; 
v_res_1847_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_1844_, v_a_1845_, v_x_1846_);
lean_dec(v_x_1846_);
lean_dec_ref(v_a_1845_);
v_r_1848_ = lean_box(v_res_1847_);
return v_r_1848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16(lean_object* v_00_u03b2_1849_, lean_object* v_data_1850_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(v_data_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17(lean_object* v_00_u03b2_1852_, lean_object* v_a_1853_, lean_object* v_b_1854_, lean_object* v_x_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_1853_, v_b_1854_, v_x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object* v_00_u03b2_1857_, lean_object* v_i_1858_, lean_object* v_source_1859_, lean_object* v_target_1860_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_1858_, v_source_1859_, v_target_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object* v_00_u03b2_1862_, lean_object* v_x_1863_, lean_object* v_x_1864_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_1863_, v_x_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0(lean_object* v_x_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___boxed(lean_object* v_x_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_Meta_Sym_foldProjs___lam__0(v_x_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec_ref(v_x_1874_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(lean_object* v_msgData_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v___x_1887_; lean_object* v_env_1888_; uint8_t v___x_1889_; lean_object* v_env_1890_; lean_object* v___x_1891_; lean_object* v_toCold_1892_; lean_object* v_mctx_1893_; lean_object* v_lctx_1894_; lean_object* v_options_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1887_ = lean_st_ref_get(v___y_1885_);
v_env_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc_ref(v_env_1888_);
lean_dec(v___x_1887_);
v___x_1889_ = 0;
v_env_1890_ = l_Lean_Environment_setRecordingDeps(v_env_1888_, v___x_1889_);
v___x_1891_ = lean_st_ref_get(v___y_1883_);
v_toCold_1892_ = lean_ctor_get(v___y_1884_, 0);
v_mctx_1893_ = lean_ctor_get(v___x_1891_, 0);
lean_inc_ref(v_mctx_1893_);
lean_dec(v___x_1891_);
v_lctx_1894_ = lean_ctor_get(v___y_1882_, 2);
v_options_1895_ = lean_ctor_get(v_toCold_1892_, 2);
lean_inc_ref(v_options_1895_);
lean_inc_ref(v_lctx_1894_);
v___x_1896_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1896_, 0, v_env_1890_);
lean_ctor_set(v___x_1896_, 1, v_mctx_1893_);
lean_ctor_set(v___x_1896_, 2, v_lctx_1894_);
lean_ctor_set(v___x_1896_, 3, v_options_1895_);
v___x_1897_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
lean_ctor_set(v___x_1897_, 1, v_msgData_1881_);
v___x_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0___boxed(lean_object* v_msgData_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msgData_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
return v_res_1905_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1906_; double v___x_1907_; 
v___x_1906_ = lean_unsigned_to_nat(0u);
v___x_1907_ = lean_float_of_nat(v___x_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(lean_object* v_cls_1911_, lean_object* v_msg_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_ref_1918_; lean_object* v___x_1919_; lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1965_; 
v_ref_1918_ = lean_ctor_get(v___y_1915_, 2);
v___x_1919_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1965_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1965_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; lean_object* v_traceState_1925_; lean_object* v_env_1926_; lean_object* v_nextMacroScope_1927_; lean_object* v_ngen_1928_; lean_object* v_auxDeclNGen_1929_; lean_object* v_cache_1930_; lean_object* v_recordedDeps_1931_; lean_object* v_messages_1932_; lean_object* v_infoState_1933_; lean_object* v_snapshotTasks_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1964_; 
v___x_1924_ = lean_st_ref_take(v___y_1916_);
v_traceState_1925_ = lean_ctor_get(v___x_1924_, 4);
v_env_1926_ = lean_ctor_get(v___x_1924_, 0);
v_nextMacroScope_1927_ = lean_ctor_get(v___x_1924_, 1);
v_ngen_1928_ = lean_ctor_get(v___x_1924_, 2);
v_auxDeclNGen_1929_ = lean_ctor_get(v___x_1924_, 3);
v_cache_1930_ = lean_ctor_get(v___x_1924_, 5);
v_recordedDeps_1931_ = lean_ctor_get(v___x_1924_, 6);
v_messages_1932_ = lean_ctor_get(v___x_1924_, 7);
v_infoState_1933_ = lean_ctor_get(v___x_1924_, 8);
v_snapshotTasks_1934_ = lean_ctor_get(v___x_1924_, 9);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1936_ = v___x_1924_;
v_isShared_1937_ = v_isSharedCheck_1964_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_snapshotTasks_1934_);
lean_inc(v_infoState_1933_);
lean_inc(v_messages_1932_);
lean_inc(v_recordedDeps_1931_);
lean_inc(v_cache_1930_);
lean_inc(v_traceState_1925_);
lean_inc(v_auxDeclNGen_1929_);
lean_inc(v_ngen_1928_);
lean_inc(v_nextMacroScope_1927_);
lean_inc(v_env_1926_);
lean_dec(v___x_1924_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1964_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
uint64_t v_tid_1938_; lean_object* v_traces_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1963_; 
v_tid_1938_ = lean_ctor_get_uint64(v_traceState_1925_, sizeof(void*)*1);
v_traces_1939_ = lean_ctor_get(v_traceState_1925_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v_traceState_1925_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1941_ = v_traceState_1925_;
v_isShared_1942_ = v_isSharedCheck_1963_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_traces_1939_);
lean_dec(v_traceState_1925_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1963_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; double v___x_1945_; uint8_t v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1954_; 
v___x_1943_ = lean_box(0);
v___x_1944_ = lean_box(0);
v___x_1945_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_1946_ = 0;
v___x_1947_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_1948_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1948_, 0, v_cls_1911_);
lean_ctor_set(v___x_1948_, 1, v___x_1944_);
lean_ctor_set(v___x_1948_, 2, v___x_1947_);
lean_ctor_set_float(v___x_1948_, sizeof(void*)*3, v___x_1945_);
lean_ctor_set_float(v___x_1948_, sizeof(void*)*3 + 8, v___x_1945_);
lean_ctor_set_uint8(v___x_1948_, sizeof(void*)*3 + 16, v___x_1946_);
v___x_1949_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
v___x_1950_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1948_);
lean_ctor_set(v___x_1950_, 1, v_a_1920_);
lean_ctor_set(v___x_1950_, 2, v___x_1949_);
lean_inc(v_ref_1918_);
v___x_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1951_, 0, v_ref_1918_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = l_Lean_PersistentArray_push___redArg(v_traces_1939_, v___x_1951_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 0, v___x_1952_);
v___x_1954_ = v___x_1941_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1952_);
lean_ctor_set_uint64(v_reuseFailAlloc_1962_, sizeof(void*)*1, v_tid_1938_);
v___x_1954_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
lean_object* v___x_1956_; 
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 4, v___x_1954_);
v___x_1956_ = v___x_1936_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_env_1926_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_nextMacroScope_1927_);
lean_ctor_set(v_reuseFailAlloc_1961_, 2, v_ngen_1928_);
lean_ctor_set(v_reuseFailAlloc_1961_, 3, v_auxDeclNGen_1929_);
lean_ctor_set(v_reuseFailAlloc_1961_, 4, v___x_1954_);
lean_ctor_set(v_reuseFailAlloc_1961_, 5, v_cache_1930_);
lean_ctor_set(v_reuseFailAlloc_1961_, 6, v_recordedDeps_1931_);
lean_ctor_set(v_reuseFailAlloc_1961_, 7, v_messages_1932_);
lean_ctor_set(v_reuseFailAlloc_1961_, 8, v_infoState_1933_);
lean_ctor_set(v_reuseFailAlloc_1961_, 9, v_snapshotTasks_1934_);
v___x_1956_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
lean_object* v___x_1957_; lean_object* v___x_1959_; 
v___x_1957_ = lean_st_ref_put(v___y_1916_, v___x_1956_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___x_1943_);
v___x_1959_ = v___x_1922_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1943_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___boxed(lean_object* v_cls_1966_, lean_object* v_msg_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v_cls_1966_, v_msg_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
return v_res_1973_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1977_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_1978_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__1));
v___x_1979_ = l_Lean_Name_append(v___x_1978_, v___x_1977_);
return v___x_1979_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__3));
v___x_1982_ = l_Lean_stringToMessageData(v___x_1981_);
return v___x_1982_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__5));
v___x_1985_ = l_Lean_stringToMessageData(v___x_1984_);
return v___x_1985_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__8(void){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__7));
v___x_1988_ = l_Lean_stringToMessageData(v___x_1987_);
return v___x_1988_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__10(void){
_start:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__9));
v___x_1991_ = l_Lean_stringToMessageData(v___x_1990_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1(lean_object* v_e_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v___y_1999_; 
if (lean_obj_tag(v_e_1992_) == 11)
{
lean_object* v_typeName_2023_; lean_object* v_idx_2024_; lean_object* v_struct_2025_; lean_object* v___x_2026_; lean_object* v_env_2027_; lean_object* v___x_2028_; 
v_typeName_2023_ = lean_ctor_get(v_e_1992_, 0);
v_idx_2024_ = lean_ctor_get(v_e_1992_, 1);
v_struct_2025_ = lean_ctor_get(v_e_1992_, 2);
v___x_2026_ = lean_st_ref_get(v___y_1996_);
v_env_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc_ref(v_env_2027_);
lean_dec(v___x_2026_);
lean_inc(v_typeName_2023_);
v___x_2028_ = l_Lean_getStructureInfo_x3f(v_env_2027_, v_typeName_2023_);
if (lean_obj_tag(v___x_2028_) == 1)
{
lean_object* v_val_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2083_; 
v_val_2029_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2031_ = v___x_2028_;
v_isShared_2032_ = v_isSharedCheck_2083_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_val_2029_);
lean_dec(v___x_2028_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2083_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v_fieldNames_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; 
v_fieldNames_2033_ = lean_ctor_get(v_val_2029_, 1);
lean_inc_ref(v_fieldNames_2033_);
lean_dec(v_val_2029_);
v___x_2034_ = lean_array_get_size(v_fieldNames_2033_);
v___x_2035_ = lean_nat_dec_lt(v_idx_2024_, v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v_toCold_2036_; lean_object* v_options_2037_; uint8_t v_hasTrace_2038_; 
lean_dec_ref(v_fieldNames_2033_);
v_toCold_2036_ = lean_ctor_get(v___y_1995_, 0);
v_options_2037_ = lean_ctor_get(v_toCold_2036_, 2);
v_hasTrace_2038_ = lean_ctor_get_uint8(v_options_2037_, sizeof(void*)*1);
if (v_hasTrace_2038_ == 0)
{
lean_del_object(v___x_2031_);
goto v___jp_2020_;
}
else
{
lean_object* v_inheritedTraceOptions_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; 
v_inheritedTraceOptions_2039_ = lean_ctor_get(v_toCold_2036_, 11);
v___x_2040_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_2041_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__2);
v___x_2042_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2039_, v_options_2037_, v___x_2041_);
if (v___x_2042_ == 0)
{
lean_del_object(v___x_2031_);
goto v___jp_2020_;
}
else
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2046_; 
v___x_2043_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__4, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__4_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__4);
lean_inc(v_idx_2024_);
v___x_2044_ = l_Nat_reprFast(v_idx_2024_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set_tag(v___x_2031_, 3);
lean_ctor_set(v___x_2031_, 0, v___x_2044_);
v___x_2046_ = v___x_2031_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2047_ = l_Lean_MessageData_ofFormat(v___x_2046_);
v___x_2048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2043_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
v___x_2049_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__6, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__6_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__6);
v___x_2050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2048_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
lean_inc_ref(v_e_1992_);
v___x_2051_ = l_Lean_indentExpr(v_e_1992_);
v___x_2052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2050_);
lean_ctor_set(v___x_2052_, 1, v___x_2051_);
v___x_2053_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v___x_2040_, v___x_2052_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_dec_ref_known(v___x_2053_, 1);
goto v___jp_2020_;
}
else
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_dec_ref_known(v_e_1992_, 3);
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_2053_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2053_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2063_; uint8_t v_transparency_2064_; lean_object* v___x_2065_; uint8_t v___x_2066_; uint8_t v___x_2067_; 
lean_inc_ref(v_struct_2025_);
lean_inc(v_idx_2024_);
lean_del_object(v___x_2031_);
lean_dec_ref_known(v_e_1992_, 3);
v___x_2063_ = l_Lean_Meta_Context_config(v___y_1993_);
v_transparency_2064_ = lean_ctor_get_uint8(v___x_2063_, 9);
lean_dec_ref(v___x_2063_);
v___x_2065_ = lean_array_fget(v_fieldNames_2033_, v_idx_2024_);
lean_dec(v_idx_2024_);
lean_dec_ref(v_fieldNames_2033_);
v___x_2066_ = 1;
v___x_2067_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2064_, v___x_2066_);
if (v___x_2067_ == 0)
{
lean_object* v_keyedConfig_2068_; uint8_t v_trackZetaDelta_2069_; lean_object* v_zetaDeltaSet_2070_; lean_object* v_lctx_2071_; lean_object* v_localInstances_2072_; lean_object* v_defEqCtx_x3f_2073_; lean_object* v_synthPendingDepth_2074_; lean_object* v_customCanUnfoldPredicate_x3f_2075_; uint8_t v_univApprox_2076_; uint8_t v_inTypeClassResolution_2077_; uint8_t v_cacheInferType_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v_keyedConfig_2068_ = lean_ctor_get(v___y_1993_, 0);
v_trackZetaDelta_2069_ = lean_ctor_get_uint8(v___y_1993_, sizeof(void*)*7);
v_zetaDeltaSet_2070_ = lean_ctor_get(v___y_1993_, 1);
v_lctx_2071_ = lean_ctor_get(v___y_1993_, 2);
v_localInstances_2072_ = lean_ctor_get(v___y_1993_, 3);
v_defEqCtx_x3f_2073_ = lean_ctor_get(v___y_1993_, 4);
v_synthPendingDepth_2074_ = lean_ctor_get(v___y_1993_, 5);
v_customCanUnfoldPredicate_x3f_2075_ = lean_ctor_get(v___y_1993_, 6);
v_univApprox_2076_ = lean_ctor_get_uint8(v___y_1993_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2077_ = lean_ctor_get_uint8(v___y_1993_, sizeof(void*)*7 + 2);
v_cacheInferType_2078_ = lean_ctor_get_uint8(v___y_1993_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2068_);
v___x_2079_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2066_, v_keyedConfig_2068_);
lean_inc(v_customCanUnfoldPredicate_x3f_2075_);
lean_inc(v_synthPendingDepth_2074_);
lean_inc(v_defEqCtx_x3f_2073_);
lean_inc_ref(v_localInstances_2072_);
lean_inc_ref(v_lctx_2071_);
lean_inc(v_zetaDeltaSet_2070_);
v___x_2080_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
lean_ctor_set(v___x_2080_, 1, v_zetaDeltaSet_2070_);
lean_ctor_set(v___x_2080_, 2, v_lctx_2071_);
lean_ctor_set(v___x_2080_, 3, v_localInstances_2072_);
lean_ctor_set(v___x_2080_, 4, v_defEqCtx_x3f_2073_);
lean_ctor_set(v___x_2080_, 5, v_synthPendingDepth_2074_);
lean_ctor_set(v___x_2080_, 6, v_customCanUnfoldPredicate_x3f_2075_);
lean_ctor_set_uint8(v___x_2080_, sizeof(void*)*7, v_trackZetaDelta_2069_);
lean_ctor_set_uint8(v___x_2080_, sizeof(void*)*7 + 1, v_univApprox_2076_);
lean_ctor_set_uint8(v___x_2080_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2077_);
lean_ctor_set_uint8(v___x_2080_, sizeof(void*)*7 + 3, v_cacheInferType_2078_);
v___x_2081_ = l_Lean_Meta_mkProjection(v_struct_2025_, v___x_2065_, v___x_2080_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec_ref_known(v___x_2080_, 7);
v___y_1999_ = v___x_2081_;
goto v___jp_1998_;
}
else
{
lean_object* v___x_2082_; 
v___x_2082_ = l_Lean_Meta_mkProjection(v_struct_2025_, v___x_2065_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
v___y_1999_ = v___x_2082_;
goto v___jp_1998_;
}
}
}
}
else
{
lean_object* v_toCold_2084_; lean_object* v_options_2085_; uint8_t v_hasTrace_2086_; 
lean_dec(v___x_2028_);
v_toCold_2084_ = lean_ctor_get(v___y_1995_, 0);
v_options_2085_ = lean_ctor_get(v_toCold_2084_, 2);
v_hasTrace_2086_ = lean_ctor_get_uint8(v_options_2085_, sizeof(void*)*1);
if (v_hasTrace_2086_ == 0)
{
goto v___jp_2017_;
}
else
{
lean_object* v_inheritedTraceOptions_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
v_inheritedTraceOptions_2087_ = lean_ctor_get(v_toCold_2084_, 11);
v___x_2088_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_2089_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__2);
v___x_2090_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2087_, v_options_2085_, v___x_2089_);
if (v___x_2090_ == 0)
{
goto v___jp_2017_;
}
else
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2091_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__8, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__8_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__8);
lean_inc(v_typeName_2023_);
v___x_2092_ = l_Lean_MessageData_ofName(v_typeName_2023_);
v___x_2093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2091_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
v___x_2094_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__10, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__10_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__10);
v___x_2095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2093_);
lean_ctor_set(v___x_2095_, 1, v___x_2094_);
lean_inc_ref(v_e_1992_);
v___x_2096_ = l_Lean_indentExpr(v_e_1992_);
v___x_2097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2095_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
v___x_2098_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v___x_2088_, v___x_2097_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_dec_ref_known(v___x_2098_, 1);
goto v___jp_2017_;
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec_ref_known(v_e_1992_, 3);
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2107_, 0, v_e_1992_);
v___x_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
return v___x_2108_;
}
v___jp_1998_:
{
if (lean_obj_tag(v___y_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2008_; 
v_a_2000_ = lean_ctor_get(v___y_1999_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___y_1999_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2002_ = v___y_1999_;
v_isShared_2003_ = v_isSharedCheck_2008_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___y_1999_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2008_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2004_; lean_object* v___x_2006_; 
v___x_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2004_, 0, v_a_2000_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v___x_2004_);
v___x_2006_ = v___x_2002_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
v_a_2009_ = lean_ctor_get(v___y_1999_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___y_1999_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___y_1999_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___y_1999_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
v___jp_2017_:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2018_, 0, v_e_1992_);
v___x_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
return v___x_2019_;
}
v___jp_2020_:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v_e_1992_);
v___x_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
return v___x_2022_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___boxed(lean_object* v_e_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l_Lean_Meta_Sym_foldProjs___lam__1(v_e_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs(lean_object* v_e_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_){
_start:
{
lean_object* v___f_2125_; lean_object* v___x_2126_; 
v___f_2125_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__0));
v___x_2126_ = lean_find_expr(v___f_2125_, v_e_2119_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v___x_2127_; 
v___x_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2127_, 0, v_e_2119_);
return v___x_2127_;
}
else
{
lean_object* v___f_2128_; lean_object* v_post_2129_; uint8_t v___x_2130_; lean_object* v___x_2131_; 
lean_dec_ref_known(v___x_2126_, 1);
v___f_2128_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__1));
v_post_2129_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__2));
v___x_2130_ = 0;
v___x_2131_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_e_2119_, v___f_2128_, v_post_2129_, v___x_2130_, v___x_2130_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_);
return v___x_2131_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___boxed(lean_object* v_e_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Lean_Meta_Sym_foldProjs(v_e_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
return v_res_2138_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2(void){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2142_ = lean_box(0);
v___x_2143_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1));
v___x_2144_ = l_Lean_mkConst(v___x_2143_, v___x_2142_);
return v___x_2144_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5(void){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2148_ = lean_box(0);
v___x_2149_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4));
v___x_2150_ = l_Lean_mkConst(v___x_2149_, v___x_2148_);
return v___x_2150_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9(void){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2156_ = lean_box(0);
v___x_2157_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8));
v___x_2158_ = l_Lean_mkConst(v___x_2157_, v___x_2156_);
return v___x_2158_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12(void){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2163_ = lean_box(0);
v___x_2164_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11));
v___x_2165_ = l_Lean_mkConst(v___x_2164_, v___x_2163_);
return v___x_2165_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13(void){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2166_ = lean_unsigned_to_nat(0u);
v___x_2167_ = l_Lean_mkNatLit(v___x_2166_);
return v___x_2167_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2173_ = lean_box(0);
v___x_2174_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16));
v___x_2175_ = l_Lean_mkConst(v___x_2174_, v___x_2173_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(lean_object* v_a_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2);
v___x_2179_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2178_, v_a_2176_, v_a_2177_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v_a_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
v_a_2181_ = lean_ctor_get(v___x_2179_, 1);
lean_inc(v_a_2181_);
lean_dec_ref_known(v___x_2179_, 2);
v___x_2182_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5);
v___x_2183_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2182_, v_a_2176_, v_a_2181_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v_a_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2184_);
v_a_2185_ = lean_ctor_get(v___x_2183_, 1);
lean_inc(v_a_2185_);
lean_dec_ref_known(v___x_2183_, 2);
v___x_2186_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9);
v___x_2187_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2186_, v_a_2176_, v_a_2185_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; lean_object* v_a_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_a_2188_);
v_a_2189_ = lean_ctor_get(v___x_2187_, 1);
lean_inc(v_a_2189_);
lean_dec_ref_known(v___x_2187_, 2);
v___x_2190_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12);
v___x_2191_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2190_, v_a_2176_, v_a_2189_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v_a_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_a_2192_);
v_a_2193_ = lean_ctor_get(v___x_2191_, 1);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2191_, 2);
v___x_2194_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13);
v___x_2195_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2194_, v_a_2176_, v_a_2193_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v_a_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
v_a_2197_ = lean_ctor_get(v___x_2195_, 1);
lean_inc(v_a_2197_);
lean_dec_ref_known(v___x_2195_, 2);
v___x_2198_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17);
v___x_2199_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2198_, v_a_2176_, v_a_2197_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v_a_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_a_2200_);
v_a_2201_ = lean_ctor_get(v___x_2199_, 1);
lean_inc(v_a_2201_);
lean_dec_ref_known(v___x_2199_, 2);
v___x_2202_ = l_Lean_Int_mkType;
v___x_2203_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_2202_, v_a_2176_, v_a_2201_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2213_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
v_a_2205_ = lean_ctor_get(v___x_2203_, 1);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2207_ = v___x_2203_;
v_isShared_2208_ = v_isSharedCheck_2213_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_inc(v_a_2204_);
lean_dec(v___x_2203_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2213_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2209_; lean_object* v___x_2211_; 
v___x_2209_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2209_, 0, v_a_2184_);
lean_ctor_set(v___x_2209_, 1, v_a_2180_);
lean_ctor_set(v___x_2209_, 2, v_a_2196_);
lean_ctor_set(v___x_2209_, 3, v_a_2192_);
lean_ctor_set(v___x_2209_, 4, v_a_2188_);
lean_ctor_set(v___x_2209_, 5, v_a_2200_);
lean_ctor_set(v___x_2209_, 6, v_a_2204_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2209_);
v___x_2211_ = v___x_2207_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2209_);
lean_ctor_set(v_reuseFailAlloc_2212_, 1, v_a_2205_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec(v_a_2200_);
lean_dec(v_a_2196_);
lean_dec(v_a_2192_);
lean_dec(v_a_2188_);
lean_dec(v_a_2184_);
lean_dec(v_a_2180_);
v_a_2214_ = lean_ctor_get(v___x_2203_, 0);
v_a_2215_ = lean_ctor_get(v___x_2203_, 1);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2203_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_inc(v_a_2214_);
lean_dec(v___x_2203_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2214_);
lean_ctor_set(v_reuseFailAlloc_2221_, 1, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_dec(v_a_2196_);
lean_dec(v_a_2192_);
lean_dec(v_a_2188_);
lean_dec(v_a_2184_);
lean_dec(v_a_2180_);
v_a_2223_ = lean_ctor_get(v___x_2199_, 0);
v_a_2224_ = lean_ctor_get(v___x_2199_, 1);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2199_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_inc(v_a_2223_);
lean_dec(v___x_2199_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2223_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v_a_2224_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
else
{
lean_object* v_a_2232_; lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec(v_a_2192_);
lean_dec(v_a_2188_);
lean_dec(v_a_2184_);
lean_dec(v_a_2180_);
v_a_2232_ = lean_ctor_get(v___x_2195_, 0);
v_a_2233_ = lean_ctor_get(v___x_2195_, 1);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2195_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_inc(v_a_2232_);
lean_dec(v___x_2195_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2232_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
else
{
lean_object* v_a_2241_; lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
lean_dec(v_a_2188_);
lean_dec(v_a_2184_);
lean_dec(v_a_2180_);
v_a_2241_ = lean_ctor_get(v___x_2191_, 0);
v_a_2242_ = lean_ctor_get(v___x_2191_, 1);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_2191_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_inc(v_a_2241_);
lean_dec(v___x_2191_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2241_);
lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_dec(v_a_2184_);
lean_dec(v_a_2180_);
v_a_2250_ = lean_ctor_get(v___x_2187_, 0);
v_a_2251_ = lean_ctor_get(v___x_2187_, 1);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2187_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_inc(v_a_2250_);
lean_dec(v___x_2187_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2250_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
else
{
lean_object* v_a_2259_; lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
lean_dec(v_a_2180_);
v_a_2259_ = lean_ctor_get(v___x_2183_, 0);
v_a_2260_ = lean_ctor_get(v___x_2183_, 1);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___x_2183_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_inc(v_a_2259_);
lean_dec(v___x_2183_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2265_; 
if (v_isShared_2263_ == 0)
{
v___x_2265_ = v___x_2262_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_a_2259_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v_a_2260_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
else
{
lean_object* v_a_2268_; lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
v_a_2268_ = lean_ctor_get(v___x_2179_, 0);
v_a_2269_ = lean_ctor_get(v___x_2179_, 1);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2179_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_inc(v_a_2268_);
lean_dec(v___x_2179_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2268_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___boxed(lean_object* v_a_2277_, lean_object* v_a_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(v_a_2277_, v_a_2278_);
lean_dec_ref(v_a_2277_);
return v_res_2279_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(lean_object* v_opts_2280_, lean_object* v_opt_2281_){
_start:
{
lean_object* v_name_2282_; lean_object* v_defValue_2283_; lean_object* v_map_2284_; lean_object* v___x_2285_; 
v_name_2282_ = lean_ctor_get(v_opt_2281_, 0);
v_defValue_2283_ = lean_ctor_get(v_opt_2281_, 1);
v_map_2284_ = lean_ctor_get(v_opts_2280_, 0);
v___x_2285_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2284_, v_name_2282_);
if (lean_obj_tag(v___x_2285_) == 0)
{
uint8_t v___x_2286_; 
v___x_2286_ = lean_unbox(v_defValue_2283_);
return v___x_2286_;
}
else
{
lean_object* v_val_2287_; 
v_val_2287_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_val_2287_);
lean_dec_ref_known(v___x_2285_, 1);
if (lean_obj_tag(v_val_2287_) == 1)
{
uint8_t v_v_2288_; 
v_v_2288_ = lean_ctor_get_uint8(v_val_2287_, 0);
lean_dec_ref_known(v_val_2287_, 0);
return v_v_2288_;
}
else
{
uint8_t v___x_2289_; 
lean_dec(v_val_2287_);
v___x_2289_ = lean_unbox(v_defValue_2283_);
return v___x_2289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0___boxed(lean_object* v_opts_2290_, lean_object* v_opt_2291_){
_start:
{
uint8_t v_res_2292_; lean_object* v_r_2293_; 
v_res_2292_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(v_opts_2290_, v_opt_2291_);
lean_dec_ref(v_opt_2291_);
lean_dec_ref(v_opts_2290_);
v_r_2293_ = lean_box(v_res_2292_);
return v_r_2293_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2294_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0);
v___x_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg(){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__1);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___boxed(lean_object* v___dummy_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg();
return v_res_2300_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg();
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1(lean_object* v_00_u03b2_2302_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(lean_object* v_msg_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v___f_2311_; lean_object* v___x_2166__overap_2312_; lean_object* v___x_2313_; 
v___f_2311_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___closed__0));
v___x_2166__overap_2312_ = lean_panic_fn_borrowed(v___f_2311_, v_msg_2305_);
lean_inc(v___y_2309_);
lean_inc_ref(v___y_2308_);
lean_inc(v___y_2307_);
lean_inc_ref(v___y_2306_);
v___x_2313_ = lean_apply_5(v___x_2166__overap_2312_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, lean_box(0));
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___boxed(lean_object* v_msg_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(v_msg_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
return v_res_2320_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0);
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
return v___x_2322_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2323_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
v___x_2324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2323_);
lean_ctor_set(v___x_2324_, 1, v___x_2323_);
return v___x_2324_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__5(void){
_start:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2328_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__4));
v___x_2329_ = lean_unsigned_to_nat(19u);
v___x_2330_ = lean_unsigned_to_nat(307u);
v___x_2331_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__3));
v___x_2332_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__2));
v___x_2333_ = l_mkPanicMessageWithDecl(v___x_2332_, v___x_2331_, v___x_2330_, v___x_2329_, v___x_2328_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object* v_x_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v_fst_2341_; lean_object* v_snd_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___x_2382_; lean_object* v_env_2383_; uint8_t v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2382_ = lean_st_ref_get(v_a_2338_);
v_env_2383_ = lean_ctor_get(v___x_2382_, 0);
lean_inc_ref(v_env_2383_);
lean_dec(v___x_2382_);
v___x_2384_ = 0;
v___x_2385_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2385_, 0, v_env_2383_);
lean_ctor_set_uint8(v___x_2385_, sizeof(void*)*1, v___x_2384_);
lean_ctor_set_uint8(v___x_2385_, sizeof(void*)*1 + 1, v___x_2384_);
v___x_2386_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0);
v___x_2387_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(v___x_2385_, v___x_2386_);
lean_dec_ref_known(v___x_2385_, 1);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v_a_2389_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_a_2388_);
v_a_2389_ = lean_ctor_get(v___x_2387_, 1);
lean_inc(v_a_2389_);
lean_dec_ref_known(v___x_2387_, 2);
v_fst_2341_ = v_a_2388_;
v_snd_2342_ = v_a_2389_;
v___y_2343_ = v_a_2335_;
v___y_2344_ = v_a_2336_;
v___y_2345_ = v_a_2337_;
v___y_2346_ = v_a_2338_;
goto v___jp_2340_;
}
else
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
lean_dec_ref_known(v___x_2387_, 2);
v___x_2390_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__5, &l_Lean_Meta_Sym_SymM_run___redArg___closed__5_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__5);
v___x_2391_ = l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(v___x_2390_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v_fst_2393_; lean_object* v_snd_2394_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref_known(v___x_2391_, 1);
v_fst_2393_ = lean_ctor_get(v_a_2392_, 0);
lean_inc(v_fst_2393_);
v_snd_2394_ = lean_ctor_get(v_a_2392_, 1);
lean_inc(v_snd_2394_);
lean_dec(v_a_2392_);
v_fst_2341_ = v_fst_2393_;
v_snd_2342_ = v_snd_2394_;
v___y_2343_ = v_a_2335_;
v___y_2344_ = v_a_2336_;
v___y_2345_ = v_a_2337_;
v___y_2346_ = v_a_2338_;
goto v___jp_2340_;
}
else
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
lean_dec_ref(v_x_2334_);
v_a_2395_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2391_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2391_);
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
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
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
}
v___jp_2340_:
{
lean_object* v_ref_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; uint8_t v___x_2350_; lean_object* v___x_2351_; 
v_ref_2347_ = lean_ctor_get(v___y_2345_, 2);
v___x_2348_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2345_);
v___x_2349_ = l_Lean_Meta_Sym_sym_debug;
v___x_2350_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(v___x_2348_, v___x_2349_);
lean_dec_ref(v___x_2348_);
v___x_2351_ = l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_a_2352_);
lean_dec_ref_known(v___x_2351_, 1);
v___x_2353_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedConfig_default___closed__0));
v___x_2354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2354_, 0, v_fst_2341_);
lean_ctor_set(v___x_2354_, 1, v___x_2353_);
v___x_2355_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__0, &l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0);
v___x_2356_ = lean_box(0);
v___x_2357_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__1, &l_Lean_Meta_Sym_SymM_run___redArg___closed__1_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1);
v___x_2358_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v___x_2358_, 0, v_snd_2342_);
lean_ctor_set(v___x_2358_, 1, v___x_2355_);
lean_ctor_set(v___x_2358_, 2, v___x_2355_);
lean_ctor_set(v___x_2358_, 3, v___x_2355_);
lean_ctor_set(v___x_2358_, 4, v___x_2355_);
lean_ctor_set(v___x_2358_, 5, v___x_2355_);
lean_ctor_set(v___x_2358_, 6, v___x_2355_);
lean_ctor_set(v___x_2358_, 7, v___x_2355_);
lean_ctor_set(v___x_2358_, 8, v_a_2352_);
lean_ctor_set(v___x_2358_, 9, v___x_2356_);
lean_ctor_set(v___x_2358_, 10, v___x_2357_);
lean_ctor_set(v___x_2358_, 11, v___x_2355_);
lean_ctor_set_uint8(v___x_2358_, sizeof(void*)*12, v___x_2350_);
v___x_2359_ = lean_st_mk_ref(v___x_2358_);
lean_inc(v___y_2346_);
lean_inc_ref(v___y_2345_);
lean_inc(v___y_2344_);
lean_inc_ref(v___y_2343_);
lean_inc(v___x_2359_);
v___x_2360_ = lean_apply_7(v_x_2334_, v___x_2354_, v___x_2359_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, lean_box(0));
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2369_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2363_ = v___x_2360_;
v_isShared_2364_ = v_isSharedCheck_2369_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2360_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2369_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2365_; lean_object* v___x_2367_; 
v___x_2365_ = lean_st_ref_get(v___x_2359_);
lean_dec(v___x_2359_);
lean_dec(v___x_2365_);
if (v_isShared_2364_ == 0)
{
v___x_2367_ = v___x_2363_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2361_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
else
{
lean_dec(v___x_2359_);
return v___x_2360_;
}
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2381_; 
lean_dec_ref(v_snd_2342_);
lean_dec_ref(v_fst_2341_);
lean_dec_ref(v_x_2334_);
v_a_2370_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2372_ = v___x_2351_;
v_isShared_2373_ = v_isSharedCheck_2381_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2351_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2381_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2379_; 
v___x_2374_ = lean_io_error_to_string(v_a_2370_);
v___x_2375_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2374_);
v___x_2376_ = l_Lean_MessageData_ofFormat(v___x_2375_);
lean_inc(v_ref_2347_);
v___x_2377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2377_, 0, v_ref_2347_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 0, v___x_2377_);
v___x_2379_ = v___x_2372_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2377_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg___boxed(lean_object* v_x_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
lean_dec(v_a_2405_);
lean_dec_ref(v_a_2404_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run(lean_object* v_00_u03b1_2410_, lean_object* v_x_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___boxed(lean_object* v_00_u03b1_2418_, lean_object* v_x_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l_Lean_Meta_Sym_SymM_run(v_00_u03b1_2418_, v_x_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
lean_dec(v_a_2423_);
lean_dec_ref(v_a_2422_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2420_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg(lean_object* v_a_2426_){
_start:
{
lean_object* v_sharedExprs_2428_; lean_object* v___x_2429_; 
v_sharedExprs_2428_ = lean_ctor_get(v_a_2426_, 0);
lean_inc_ref(v_sharedExprs_2428_);
v___x_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2429_, 0, v_sharedExprs_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg___boxed(lean_object* v_a_2430_, lean_object* v_a_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2430_);
lean_dec_ref(v_a_2430_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs(lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2433_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___boxed(lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_Meta_Sym_getSharedExprs(v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_);
lean_dec(v_a_2446_);
lean_dec_ref(v_a_2445_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object* v_a_2449_){
_start:
{
lean_object* v___x_2451_; lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2460_; 
v___x_2451_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2449_);
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2454_ = v___x_2451_;
v_isShared_2455_ = v_isSharedCheck_2460_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2451_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2460_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v_trueExpr_2456_; lean_object* v___x_2458_; 
v_trueExpr_2456_ = lean_ctor_get(v_a_2452_, 0);
lean_inc_ref(v_trueExpr_2456_);
lean_dec(v_a_2452_);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 0, v_trueExpr_2456_);
v___x_2458_ = v___x_2454_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_trueExpr_2456_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg___boxed(lean_object* v_a_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2461_);
lean_dec_ref(v_a_2461_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr(lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2464_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___boxed(lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Lean_Meta_Sym_getTrueExpr(v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_);
lean_dec(v_a_2477_);
lean_dec_ref(v_a_2476_);
lean_dec(v_a_2475_);
lean_dec_ref(v_a_2474_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object* v_e_2480_, lean_object* v_a_2481_){
_start:
{
lean_object* v___x_2483_; 
v___x_2483_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2481_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2495_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2486_ = v___x_2483_;
v_isShared_2487_ = v_isSharedCheck_2495_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2483_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2495_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
size_t v___x_2488_; size_t v___x_2489_; uint8_t v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2493_; 
v___x_2488_ = lean_ptr_addr(v_e_2480_);
v___x_2489_ = lean_ptr_addr(v_a_2484_);
lean_dec(v_a_2484_);
v___x_2490_ = lean_usize_dec_eq(v___x_2488_, v___x_2489_);
v___x_2491_ = lean_box(v___x_2490_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 0, v___x_2491_);
v___x_2493_ = v___x_2486_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___x_2491_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
v_a_2496_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2483_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2483_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg___boxed(lean_object* v_e_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_2504_, v_a_2505_);
lean_dec_ref(v_a_2505_);
lean_dec_ref(v_e_2504_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr(lean_object* v_e_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_){
_start:
{
lean_object* v___x_2516_; 
v___x_2516_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_2508_, v_a_2509_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___boxed(lean_object* v_e_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Lean_Meta_Sym_isTrueExpr(v_e_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
lean_dec(v_a_2521_);
lean_dec_ref(v_a_2520_);
lean_dec(v_a_2519_);
lean_dec_ref(v_a_2518_);
lean_dec_ref(v_e_2517_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object* v_a_2526_){
_start:
{
lean_object* v___x_2528_; lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2537_; 
v___x_2528_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2526_);
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2531_ = v___x_2528_;
v_isShared_2532_ = v_isSharedCheck_2537_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2528_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2537_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v_falseExpr_2533_; lean_object* v___x_2535_; 
v_falseExpr_2533_ = lean_ctor_get(v_a_2529_, 1);
lean_inc_ref(v_falseExpr_2533_);
lean_dec(v_a_2529_);
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 0, v_falseExpr_2533_);
v___x_2535_ = v___x_2531_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_falseExpr_2533_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg___boxed(lean_object* v_a_2538_, lean_object* v_a_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2538_);
lean_dec_ref(v_a_2538_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr(lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_){
_start:
{
lean_object* v___x_2548_; 
v___x_2548_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2541_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___boxed(lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_Lean_Meta_Sym_getFalseExpr(v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
lean_dec(v_a_2554_);
lean_dec_ref(v_a_2553_);
lean_dec(v_a_2552_);
lean_dec_ref(v_a_2551_);
lean_dec(v_a_2550_);
lean_dec_ref(v_a_2549_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object* v_e_2557_, lean_object* v_a_2558_){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2558_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2572_; 
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2563_ = v___x_2560_;
v_isShared_2564_ = v_isSharedCheck_2572_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2560_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2572_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
size_t v___x_2565_; size_t v___x_2566_; uint8_t v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2570_; 
v___x_2565_ = lean_ptr_addr(v_e_2557_);
v___x_2566_ = lean_ptr_addr(v_a_2561_);
lean_dec(v_a_2561_);
v___x_2567_ = lean_usize_dec_eq(v___x_2565_, v___x_2566_);
v___x_2568_ = lean_box(v___x_2567_);
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 0, v___x_2568_);
v___x_2570_ = v___x_2563_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___x_2568_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
v_a_2573_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___x_2560_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2560_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2573_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg___boxed(lean_object* v_e_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_2581_, v_a_2582_);
lean_dec_ref(v_a_2582_);
lean_dec_ref(v_e_2581_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr(lean_object* v_e_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_){
_start:
{
lean_object* v___x_2593_; 
v___x_2593_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_2585_, v_a_2586_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___boxed(lean_object* v_e_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_Meta_Sym_isFalseExpr(v_e_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_);
lean_dec(v_a_2600_);
lean_dec_ref(v_a_2599_);
lean_dec(v_a_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_a_2596_);
lean_dec_ref(v_a_2595_);
lean_dec_ref(v_e_2594_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object* v_a_2603_){
_start:
{
lean_object* v___x_2605_; lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2614_; 
v___x_2605_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2603_);
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2608_ = v___x_2605_;
v_isShared_2609_ = v_isSharedCheck_2614_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2605_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2614_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v_btrueExpr_2610_; lean_object* v___x_2612_; 
v_btrueExpr_2610_ = lean_ctor_get(v_a_2606_, 3);
lean_inc_ref(v_btrueExpr_2610_);
lean_dec(v_a_2606_);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v_btrueExpr_2610_);
v___x_2612_ = v___x_2608_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_btrueExpr_2610_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg___boxed(lean_object* v_a_2615_, lean_object* v_a_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2615_);
lean_dec_ref(v_a_2615_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr(lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_){
_start:
{
lean_object* v___x_2625_; 
v___x_2625_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2618_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___boxed(lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Lean_Meta_Sym_getBoolTrueExpr(v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_);
lean_dec(v_a_2631_);
lean_dec_ref(v_a_2630_);
lean_dec(v_a_2629_);
lean_dec_ref(v_a_2628_);
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg(lean_object* v_e_2634_, lean_object* v_a_2635_){
_start:
{
lean_object* v___x_2637_; 
v___x_2637_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2635_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2649_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2640_ = v___x_2637_;
v_isShared_2641_ = v_isSharedCheck_2649_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2637_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2649_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
size_t v___x_2642_; size_t v___x_2643_; uint8_t v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2647_; 
v___x_2642_ = lean_ptr_addr(v_e_2634_);
v___x_2643_ = lean_ptr_addr(v_a_2638_);
lean_dec(v_a_2638_);
v___x_2644_ = lean_usize_dec_eq(v___x_2642_, v___x_2643_);
v___x_2645_ = lean_box(v___x_2644_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 0, v___x_2645_);
v___x_2647_ = v___x_2640_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2645_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
v_a_2650_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2637_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2637_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg___boxed(lean_object* v_e_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_2658_, v_a_2659_);
lean_dec_ref(v_a_2659_);
lean_dec_ref(v_e_2658_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr(lean_object* v_e_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_2662_, v_a_2663_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___boxed(lean_object* v_e_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_Lean_Meta_Sym_isBoolTrueExpr(v_e_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
lean_dec(v_a_2675_);
lean_dec_ref(v_a_2674_);
lean_dec(v_a_2673_);
lean_dec_ref(v_a_2672_);
lean_dec_ref(v_e_2671_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object* v_a_2680_){
_start:
{
lean_object* v___x_2682_; lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2691_; 
v___x_2682_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2680_);
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2685_ = v___x_2682_;
v_isShared_2686_ = v_isSharedCheck_2691_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2682_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2691_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v_bfalseExpr_2687_; lean_object* v___x_2689_; 
v_bfalseExpr_2687_ = lean_ctor_get(v_a_2683_, 4);
lean_inc_ref(v_bfalseExpr_2687_);
lean_dec(v_a_2683_);
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 0, v_bfalseExpr_2687_);
v___x_2689_ = v___x_2685_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_bfalseExpr_2687_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg___boxed(lean_object* v_a_2692_, lean_object* v_a_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2692_);
lean_dec_ref(v_a_2692_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr(lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2695_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___boxed(lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_Lean_Meta_Sym_getBoolFalseExpr(v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
lean_dec(v_a_2708_);
lean_dec_ref(v_a_2707_);
lean_dec(v_a_2706_);
lean_dec_ref(v_a_2705_);
lean_dec(v_a_2704_);
lean_dec_ref(v_a_2703_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg(lean_object* v_e_2711_, lean_object* v_a_2712_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2712_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2726_; 
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2717_ = v___x_2714_;
v_isShared_2718_ = v_isSharedCheck_2726_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2714_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2726_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
size_t v___x_2719_; size_t v___x_2720_; uint8_t v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2719_ = lean_ptr_addr(v_e_2711_);
v___x_2720_ = lean_ptr_addr(v_a_2715_);
lean_dec(v_a_2715_);
v___x_2721_ = lean_usize_dec_eq(v___x_2719_, v___x_2720_);
v___x_2722_ = lean_box(v___x_2721_);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 0, v___x_2722_);
v___x_2724_ = v___x_2717_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
else
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2734_; 
v_a_2727_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2729_ = v___x_2714_;
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2714_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2727_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg___boxed(lean_object* v_e_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_2735_, v_a_2736_);
lean_dec_ref(v_a_2736_);
lean_dec_ref(v_e_2735_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr(lean_object* v_e_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_){
_start:
{
lean_object* v___x_2747_; 
v___x_2747_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_2739_, v_a_2740_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___boxed(lean_object* v_e_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_Lean_Meta_Sym_isBoolFalseExpr(v_e_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_);
lean_dec(v_a_2754_);
lean_dec_ref(v_a_2753_);
lean_dec(v_a_2752_);
lean_dec_ref(v_a_2751_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
lean_dec_ref(v_e_2748_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg(lean_object* v_a_2757_){
_start:
{
lean_object* v___x_2759_; lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2768_; 
v___x_2759_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2757_);
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2762_ = v___x_2759_;
v_isShared_2763_ = v_isSharedCheck_2768_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2759_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2768_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v_natZExpr_2764_; lean_object* v___x_2766_; 
v_natZExpr_2764_ = lean_ctor_get(v_a_2760_, 2);
lean_inc_ref(v_natZExpr_2764_);
lean_dec(v_a_2760_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v_natZExpr_2764_);
v___x_2766_ = v___x_2762_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_natZExpr_2764_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg___boxed(lean_object* v_a_2769_, lean_object* v_a_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_2769_);
lean_dec_ref(v_a_2769_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr(lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_){
_start:
{
lean_object* v___x_2779_; 
v___x_2779_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_2772_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___boxed(lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Lean_Meta_Sym_getNatZeroExpr(v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_);
lean_dec(v_a_2785_);
lean_dec_ref(v_a_2784_);
lean_dec(v_a_2783_);
lean_dec_ref(v_a_2782_);
lean_dec(v_a_2781_);
lean_dec_ref(v_a_2780_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg(lean_object* v_a_2788_){
_start:
{
lean_object* v___x_2790_; lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2799_; 
v___x_2790_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2788_);
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2793_ = v___x_2790_;
v_isShared_2794_ = v_isSharedCheck_2799_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2790_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2799_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v_ordEqExpr_2795_; lean_object* v___x_2797_; 
v_ordEqExpr_2795_ = lean_ctor_get(v_a_2791_, 5);
lean_inc_ref(v_ordEqExpr_2795_);
lean_dec(v_a_2791_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v_ordEqExpr_2795_);
v___x_2797_ = v___x_2793_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_ordEqExpr_2795_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg___boxed(lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_2800_);
lean_dec_ref(v_a_2800_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr(lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_2803_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___boxed(lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_Lean_Meta_Sym_getOrderingEqExpr(v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_);
lean_dec(v_a_2816_);
lean_dec_ref(v_a_2815_);
lean_dec(v_a_2814_);
lean_dec_ref(v_a_2813_);
lean_dec(v_a_2812_);
lean_dec_ref(v_a_2811_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg(lean_object* v_a_2819_){
_start:
{
lean_object* v___x_2821_; lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2830_; 
v___x_2821_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2819_);
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2824_ = v___x_2821_;
v_isShared_2825_ = v_isSharedCheck_2830_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2821_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2830_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v_intExpr_2826_; lean_object* v___x_2828_; 
v_intExpr_2826_ = lean_ctor_get(v_a_2822_, 6);
lean_inc_ref(v_intExpr_2826_);
lean_dec(v_a_2822_);
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 0, v_intExpr_2826_);
v___x_2828_ = v___x_2824_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_intExpr_2826_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg___boxed(lean_object* v_a_2831_, lean_object* v_a_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_2831_);
lean_dec_ref(v_a_2831_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr(lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_2834_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___boxed(lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_Lean_Meta_Sym_getIntExpr(v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
lean_dec(v_a_2847_);
lean_dec_ref(v_a_2846_);
lean_dec(v_a_2845_);
lean_dec_ref(v_a_2844_);
lean_dec(v_a_2843_);
lean_dec_ref(v_a_2842_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg(lean_object* v_k_2850_, lean_object* v_ctx_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v___x_2854_; lean_object* v_share_2855_; lean_object* v_maxFVar_2856_; lean_object* v_proofInstInfo_2857_; lean_object* v_proofInstInfoFVar_2858_; lean_object* v_inferType_2859_; lean_object* v_getLevel_2860_; lean_object* v_congrInfo_2861_; lean_object* v_defEqI_2862_; lean_object* v_extensions_2863_; lean_object* v_issues_2864_; lean_object* v_canon_2865_; lean_object* v_instanceOverrides_2866_; uint8_t v_debug_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2929_; 
v___x_2854_ = lean_st_ref_take(v_a_2852_);
v_share_2855_ = lean_ctor_get(v___x_2854_, 0);
v_maxFVar_2856_ = lean_ctor_get(v___x_2854_, 1);
v_proofInstInfo_2857_ = lean_ctor_get(v___x_2854_, 2);
v_proofInstInfoFVar_2858_ = lean_ctor_get(v___x_2854_, 3);
v_inferType_2859_ = lean_ctor_get(v___x_2854_, 4);
v_getLevel_2860_ = lean_ctor_get(v___x_2854_, 5);
v_congrInfo_2861_ = lean_ctor_get(v___x_2854_, 6);
v_defEqI_2862_ = lean_ctor_get(v___x_2854_, 7);
v_extensions_2863_ = lean_ctor_get(v___x_2854_, 8);
v_issues_2864_ = lean_ctor_get(v___x_2854_, 9);
v_canon_2865_ = lean_ctor_get(v___x_2854_, 10);
v_instanceOverrides_2866_ = lean_ctor_get(v___x_2854_, 11);
v_debug_2867_ = lean_ctor_get_uint8(v___x_2854_, sizeof(void*)*12);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2869_ = v___x_2854_;
v_isShared_2870_ = v_isSharedCheck_2929_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_instanceOverrides_2866_);
lean_inc(v_canon_2865_);
lean_inc(v_issues_2864_);
lean_inc(v_extensions_2863_);
lean_inc(v_defEqI_2862_);
lean_inc(v_congrInfo_2861_);
lean_inc(v_getLevel_2860_);
lean_inc(v_inferType_2859_);
lean_inc(v_proofInstInfoFVar_2858_);
lean_inc(v_proofInstInfo_2857_);
lean_inc(v_maxFVar_2856_);
lean_inc(v_share_2855_);
lean_dec(v___x_2854_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2929_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2871_; lean_object* v___x_2873_; 
v___x_2871_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 0, v___x_2871_);
v___x_2873_ = v___x_2869_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v___x_2871_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v_maxFVar_2856_);
lean_ctor_set(v_reuseFailAlloc_2928_, 2, v_proofInstInfo_2857_);
lean_ctor_set(v_reuseFailAlloc_2928_, 3, v_proofInstInfoFVar_2858_);
lean_ctor_set(v_reuseFailAlloc_2928_, 4, v_inferType_2859_);
lean_ctor_set(v_reuseFailAlloc_2928_, 5, v_getLevel_2860_);
lean_ctor_set(v_reuseFailAlloc_2928_, 6, v_congrInfo_2861_);
lean_ctor_set(v_reuseFailAlloc_2928_, 7, v_defEqI_2862_);
lean_ctor_set(v_reuseFailAlloc_2928_, 8, v_extensions_2863_);
lean_ctor_set(v_reuseFailAlloc_2928_, 9, v_issues_2864_);
lean_ctor_set(v_reuseFailAlloc_2928_, 10, v_canon_2865_);
lean_ctor_set(v_reuseFailAlloc_2928_, 11, v_instanceOverrides_2866_);
lean_ctor_set_uint8(v_reuseFailAlloc_2928_, sizeof(void*)*12, v_debug_2867_);
v___x_2873_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2874_ = lean_st_ref_put(v_a_2852_, v___x_2873_);
v___x_2875_ = lean_apply_2(v_k_2850_, v_ctx_2851_, v_share_2855_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v_a_2877_; lean_object* v___x_2878_; lean_object* v_maxFVar_2879_; lean_object* v_proofInstInfo_2880_; lean_object* v_proofInstInfoFVar_2881_; lean_object* v_inferType_2882_; lean_object* v_getLevel_2883_; lean_object* v_congrInfo_2884_; lean_object* v_defEqI_2885_; lean_object* v_extensions_2886_; lean_object* v_issues_2887_; lean_object* v_canon_2888_; lean_object* v_instanceOverrides_2889_; uint8_t v_debug_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2900_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_a_2876_);
v_a_2877_ = lean_ctor_get(v___x_2875_, 1);
lean_inc(v_a_2877_);
lean_dec_ref_known(v___x_2875_, 2);
v___x_2878_ = lean_st_ref_take(v_a_2852_);
v_maxFVar_2879_ = lean_ctor_get(v___x_2878_, 1);
v_proofInstInfo_2880_ = lean_ctor_get(v___x_2878_, 2);
v_proofInstInfoFVar_2881_ = lean_ctor_get(v___x_2878_, 3);
v_inferType_2882_ = lean_ctor_get(v___x_2878_, 4);
v_getLevel_2883_ = lean_ctor_get(v___x_2878_, 5);
v_congrInfo_2884_ = lean_ctor_get(v___x_2878_, 6);
v_defEqI_2885_ = lean_ctor_get(v___x_2878_, 7);
v_extensions_2886_ = lean_ctor_get(v___x_2878_, 8);
v_issues_2887_ = lean_ctor_get(v___x_2878_, 9);
v_canon_2888_ = lean_ctor_get(v___x_2878_, 10);
v_instanceOverrides_2889_ = lean_ctor_get(v___x_2878_, 11);
v_debug_2890_ = lean_ctor_get_uint8(v___x_2878_, sizeof(void*)*12);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2900_ == 0)
{
lean_object* v_unused_2901_; 
v_unused_2901_ = lean_ctor_get(v___x_2878_, 0);
lean_dec(v_unused_2901_);
v___x_2892_ = v___x_2878_;
v_isShared_2893_ = v_isSharedCheck_2900_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_instanceOverrides_2889_);
lean_inc(v_canon_2888_);
lean_inc(v_issues_2887_);
lean_inc(v_extensions_2886_);
lean_inc(v_defEqI_2885_);
lean_inc(v_congrInfo_2884_);
lean_inc(v_getLevel_2883_);
lean_inc(v_inferType_2882_);
lean_inc(v_proofInstInfoFVar_2881_);
lean_inc(v_proofInstInfo_2880_);
lean_inc(v_maxFVar_2879_);
lean_dec(v___x_2878_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2900_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 0, v_a_2877_);
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2877_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v_maxFVar_2879_);
lean_ctor_set(v_reuseFailAlloc_2899_, 2, v_proofInstInfo_2880_);
lean_ctor_set(v_reuseFailAlloc_2899_, 3, v_proofInstInfoFVar_2881_);
lean_ctor_set(v_reuseFailAlloc_2899_, 4, v_inferType_2882_);
lean_ctor_set(v_reuseFailAlloc_2899_, 5, v_getLevel_2883_);
lean_ctor_set(v_reuseFailAlloc_2899_, 6, v_congrInfo_2884_);
lean_ctor_set(v_reuseFailAlloc_2899_, 7, v_defEqI_2885_);
lean_ctor_set(v_reuseFailAlloc_2899_, 8, v_extensions_2886_);
lean_ctor_set(v_reuseFailAlloc_2899_, 9, v_issues_2887_);
lean_ctor_set(v_reuseFailAlloc_2899_, 10, v_canon_2888_);
lean_ctor_set(v_reuseFailAlloc_2899_, 11, v_instanceOverrides_2889_);
lean_ctor_set_uint8(v_reuseFailAlloc_2899_, sizeof(void*)*12, v_debug_2890_);
v___x_2895_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2896_ = lean_st_ref_put(v_a_2852_, v___x_2895_);
v___x_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2897_, 0, v_a_2876_);
v___x_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
return v___x_2898_;
}
}
}
else
{
lean_object* v_a_2902_; lean_object* v_a_2903_; lean_object* v___x_2904_; lean_object* v_maxFVar_2905_; lean_object* v_proofInstInfo_2906_; lean_object* v_proofInstInfoFVar_2907_; lean_object* v_inferType_2908_; lean_object* v_getLevel_2909_; lean_object* v_congrInfo_2910_; lean_object* v_defEqI_2911_; lean_object* v_extensions_2912_; lean_object* v_issues_2913_; lean_object* v_canon_2914_; lean_object* v_instanceOverrides_2915_; uint8_t v_debug_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2926_; 
v_a_2902_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_a_2902_);
v_a_2903_ = lean_ctor_get(v___x_2875_, 1);
lean_inc(v_a_2903_);
lean_dec_ref_known(v___x_2875_, 2);
v___x_2904_ = lean_st_ref_take(v_a_2852_);
v_maxFVar_2905_ = lean_ctor_get(v___x_2904_, 1);
v_proofInstInfo_2906_ = lean_ctor_get(v___x_2904_, 2);
v_proofInstInfoFVar_2907_ = lean_ctor_get(v___x_2904_, 3);
v_inferType_2908_ = lean_ctor_get(v___x_2904_, 4);
v_getLevel_2909_ = lean_ctor_get(v___x_2904_, 5);
v_congrInfo_2910_ = lean_ctor_get(v___x_2904_, 6);
v_defEqI_2911_ = lean_ctor_get(v___x_2904_, 7);
v_extensions_2912_ = lean_ctor_get(v___x_2904_, 8);
v_issues_2913_ = lean_ctor_get(v___x_2904_, 9);
v_canon_2914_ = lean_ctor_get(v___x_2904_, 10);
v_instanceOverrides_2915_ = lean_ctor_get(v___x_2904_, 11);
v_debug_2916_ = lean_ctor_get_uint8(v___x_2904_, sizeof(void*)*12);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2926_ == 0)
{
lean_object* v_unused_2927_; 
v_unused_2927_ = lean_ctor_get(v___x_2904_, 0);
lean_dec(v_unused_2927_);
v___x_2918_ = v___x_2904_;
v_isShared_2919_ = v_isSharedCheck_2926_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_instanceOverrides_2915_);
lean_inc(v_canon_2914_);
lean_inc(v_issues_2913_);
lean_inc(v_extensions_2912_);
lean_inc(v_defEqI_2911_);
lean_inc(v_congrInfo_2910_);
lean_inc(v_getLevel_2909_);
lean_inc(v_inferType_2908_);
lean_inc(v_proofInstInfoFVar_2907_);
lean_inc(v_proofInstInfo_2906_);
lean_inc(v_maxFVar_2905_);
lean_dec(v___x_2904_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2926_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 0, v_a_2903_);
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2903_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v_maxFVar_2905_);
lean_ctor_set(v_reuseFailAlloc_2925_, 2, v_proofInstInfo_2906_);
lean_ctor_set(v_reuseFailAlloc_2925_, 3, v_proofInstInfoFVar_2907_);
lean_ctor_set(v_reuseFailAlloc_2925_, 4, v_inferType_2908_);
lean_ctor_set(v_reuseFailAlloc_2925_, 5, v_getLevel_2909_);
lean_ctor_set(v_reuseFailAlloc_2925_, 6, v_congrInfo_2910_);
lean_ctor_set(v_reuseFailAlloc_2925_, 7, v_defEqI_2911_);
lean_ctor_set(v_reuseFailAlloc_2925_, 8, v_extensions_2912_);
lean_ctor_set(v_reuseFailAlloc_2925_, 9, v_issues_2913_);
lean_ctor_set(v_reuseFailAlloc_2925_, 10, v_canon_2914_);
lean_ctor_set(v_reuseFailAlloc_2925_, 11, v_instanceOverrides_2915_);
lean_ctor_set_uint8(v_reuseFailAlloc_2925_, sizeof(void*)*12, v_debug_2916_);
v___x_2921_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2922_ = lean_st_ref_put(v_a_2852_, v___x_2921_);
v___x_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2923_, 0, v_a_2902_);
v___x_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
return v___x_2924_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg___boxed(lean_object* v_k_2930_, lean_object* v_ctx_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v_k_2930_, v_ctx_2931_, v_a_2932_);
lean_dec(v_a_2932_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM(lean_object* v_00_u03b1_2935_, lean_object* v_k_2936_, lean_object* v_ctx_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_){
_start:
{
lean_object* v___x_2945_; 
v___x_2945_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v_k_2936_, v_ctx_2937_, v_a_2939_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___boxed(lean_object* v_00_u03b1_2946_, lean_object* v_k_2947_, lean_object* v_ctx_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_){
_start:
{
lean_object* v_res_2956_; 
v_res_2956_ = l_Lean_Meta_Sym_runShareCommonM(v_00_u03b1_2946_, v_k_2947_, v_ctx_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
lean_dec(v_a_2952_);
lean_dec_ref(v_a_2951_);
lean_dec(v_a_2950_);
lean_dec_ref(v_a_2949_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___lam__0(lean_object* v_ctx_2957_){
_start:
{
lean_object* v_config_2958_; lean_object* v_sharedExprs_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2976_; 
v_config_2958_ = lean_ctor_get(v_ctx_2957_, 1);
v_sharedExprs_2959_ = lean_ctor_get(v_ctx_2957_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v_ctx_2957_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2961_ = v_ctx_2957_;
v_isShared_2962_ = v_isSharedCheck_2976_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_config_2958_);
lean_inc(v_sharedExprs_2959_);
lean_dec(v_ctx_2957_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2976_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
uint8_t v_verbose_2963_; uint8_t v_enforceUnfoldReducible_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2975_; 
v_verbose_2963_ = lean_ctor_get_uint8(v_config_2958_, 0);
v_enforceUnfoldReducible_2964_ = lean_ctor_get_uint8(v_config_2958_, 1);
v_isSharedCheck_2975_ = !lean_is_exclusive(v_config_2958_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2966_ = v_config_2958_;
v_isShared_2967_ = v_isSharedCheck_2975_;
goto v_resetjp_2965_;
}
else
{
lean_dec(v_config_2958_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2975_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
uint8_t v___x_2968_; lean_object* v___x_2970_; 
v___x_2968_ = 0;
if (v_isShared_2967_ == 0)
{
v___x_2970_ = v___x_2966_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_2974_, 0, v_verbose_2963_);
lean_ctor_set_uint8(v_reuseFailAlloc_2974_, 1, v_enforceUnfoldReducible_2964_);
v___x_2970_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2972_; 
lean_ctor_set_uint8(v___x_2970_, 2, v___x_2968_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 1, v___x_2970_);
v___x_2972_ = v___x_2961_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_sharedExprs_2959_);
lean_ctor_set(v_reuseFailAlloc_2973_, 1, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg(lean_object* v_inst_2978_, lean_object* v_x_2979_){
_start:
{
lean_object* v___f_2980_; lean_object* v___x_2981_; 
v___f_2980_ = ((lean_object*)(l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___closed__0));
v___x_2981_ = lean_apply_3(v_inst_2978_, lean_box(0), v___f_2980_, v_x_2979_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck(lean_object* v_m_2982_, lean_object* v_00_u03b1_2983_, lean_object* v_inst_2984_, lean_object* v_x_2985_){
_start:
{
lean_object* v___x_2986_; 
v___x_2986_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg(v_inst_2984_, v_x_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___lam__0(lean_object* v_ctx_2987_){
_start:
{
lean_object* v_config_2988_; lean_object* v_sharedExprs_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_3005_; 
v_config_2988_ = lean_ctor_get(v_ctx_2987_, 1);
v_sharedExprs_2989_ = lean_ctor_get(v_ctx_2987_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v_ctx_2987_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_2991_ = v_ctx_2987_;
v_isShared_2992_ = v_isSharedCheck_3005_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_config_2988_);
lean_inc(v_sharedExprs_2989_);
lean_dec(v_ctx_2987_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_3005_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
uint8_t v_verbose_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3004_; 
v_verbose_2993_ = lean_ctor_get_uint8(v_config_2988_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v_config_2988_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2995_ = v_config_2988_;
v_isShared_2996_ = v_isSharedCheck_3004_;
goto v_resetjp_2994_;
}
else
{
lean_dec(v_config_2988_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3004_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
uint8_t v___x_2997_; lean_object* v___x_2999_; 
v___x_2997_ = 0;
if (v_isShared_2996_ == 0)
{
v___x_2999_ = v___x_2995_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3003_, 0, v_verbose_2993_);
v___x_2999_ = v_reuseFailAlloc_3003_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
lean_object* v___x_3001_; 
lean_ctor_set_uint8(v___x_2999_, 1, v___x_2997_);
lean_ctor_set_uint8(v___x_2999_, 2, v___x_2997_);
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 1, v___x_2999_);
v___x_3001_ = v___x_2991_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_sharedExprs_2989_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v___x_2999_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg(lean_object* v_inst_3007_, lean_object* v_x_3008_){
_start:
{
lean_object* v___f_3009_; lean_object* v___x_3010_; 
v___f_3009_ = ((lean_object*)(l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___closed__0));
v___x_3010_ = lean_apply_3(v_inst_3007_, lean_box(0), v___f_3009_, v_x_3008_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks(lean_object* v_m_3011_, lean_object* v_00_u03b1_3012_, lean_object* v_inst_3013_, lean_object* v_x_3014_){
_start:
{
lean_object* v___x_3015_; 
v___x_3015_ = l_Lean_Meta_Sym_withoutShareCommonChecks___redArg(v_inst_3013_, v_x_3014_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(lean_object* v_a_3016_, lean_object* v_a_3017_){
_start:
{
lean_object* v_config_3019_; lean_object* v___x_3020_; lean_object* v_env_3021_; uint8_t v_enforceUnfoldReducible_3022_; uint8_t v_enforceFoldProjs_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v_config_3019_ = lean_ctor_get(v_a_3016_, 1);
v___x_3020_ = lean_st_ref_get(v_a_3017_);
v_env_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc_ref(v_env_3021_);
lean_dec(v___x_3020_);
v_enforceUnfoldReducible_3022_ = lean_ctor_get_uint8(v_config_3019_, 1);
v_enforceFoldProjs_3023_ = lean_ctor_get_uint8(v_config_3019_, 2);
v___x_3024_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3024_, 0, v_env_3021_);
lean_ctor_set_uint8(v___x_3024_, sizeof(void*)*1, v_enforceUnfoldReducible_3022_);
lean_ctor_set_uint8(v___x_3024_, sizeof(void*)*1 + 1, v_enforceFoldProjs_3023_);
v___x_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3024_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg___boxed(lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3026_, v_a_3027_);
lean_dec(v_a_3027_);
lean_dec_ref(v_a_3026_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx(lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_){
_start:
{
lean_object* v___x_3037_; 
v___x_3037_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3030_, v_a_3035_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___boxed(lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx(v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_);
lean_dec(v_a_3043_);
lean_dec_ref(v_a_3042_);
lean_dec(v_a_3041_);
lean_dec_ref(v_a_3040_);
lean_dec(v_a_3039_);
lean_dec_ref(v_a_3038_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(lean_object* v_e_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_){
_start:
{
lean_object* v_config_3053_; uint8_t v_enforceUnfoldReducible_3054_; uint8_t v_enforceFoldProjs_3055_; lean_object* v_e_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v_e_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; 
v_config_3053_ = lean_ctor_get(v_a_3047_, 1);
v_enforceUnfoldReducible_3054_ = lean_ctor_get_uint8(v_config_3053_, 1);
v_enforceFoldProjs_3055_ = lean_ctor_get_uint8(v_config_3053_, 2);
if (v_enforceUnfoldReducible_3054_ == 0)
{
v_e_3065_ = v_e_3046_;
v___y_3066_ = v_a_3048_;
v___y_3067_ = v_a_3049_;
v___y_3068_ = v_a_3050_;
v___y_3069_ = v_a_3051_;
goto v___jp_3064_;
}
else
{
lean_object* v___x_3072_; 
v___x_3072_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3046_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v_a_3073_; 
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_a_3073_);
lean_dec_ref_known(v___x_3072_, 1);
v_e_3065_ = v_a_3073_;
v___y_3066_ = v_a_3048_;
v___y_3067_ = v_a_3049_;
v___y_3068_ = v_a_3050_;
v___y_3069_ = v_a_3051_;
goto v___jp_3064_;
}
else
{
return v___x_3072_;
}
}
v___jp_3056_:
{
if (v_enforceUnfoldReducible_3054_ == 0)
{
lean_object* v___x_3062_; 
v___x_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3062_, 0, v_e_3057_);
return v___x_3062_;
}
else
{
lean_object* v___x_3063_; 
v___x_3063_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
return v___x_3063_;
}
}
v___jp_3064_:
{
if (v_enforceFoldProjs_3055_ == 0)
{
v_e_3057_ = v_e_3065_;
v___y_3058_ = v___y_3066_;
v___y_3059_ = v___y_3067_;
v___y_3060_ = v___y_3068_;
v___y_3061_ = v___y_3069_;
goto v___jp_3056_;
}
else
{
lean_object* v___x_3070_; 
v___x_3070_ = l_Lean_Meta_Sym_foldProjs(v_e_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v_a_3071_; 
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_a_3071_);
lean_dec_ref_known(v___x_3070_, 1);
v_e_3057_ = v_a_3071_;
v___y_3058_ = v___y_3066_;
v___y_3059_ = v___y_3067_;
v___y_3060_ = v___y_3068_;
v___y_3061_ = v___y_3069_;
goto v___jp_3056_;
}
else
{
return v___x_3070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg___boxed(lean_object* v_e_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
lean_dec(v_a_3079_);
lean_dec_ref(v_a_3078_);
lean_dec(v_a_3077_);
lean_dec_ref(v_a_3076_);
lean_dec_ref(v_a_3075_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation(lean_object* v_e_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_){
_start:
{
lean_object* v___x_3090_; 
v___x_3090_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3082_, v_a_3083_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___boxed(lean_object* v_e_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation(v_e_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_);
lean_dec(v_a_3097_);
lean_dec_ref(v_a_3096_);
lean_dec(v_a_3095_);
lean_dec_ref(v_a_3094_);
lean_dec(v_a_3093_);
lean_dec_ref(v_a_3092_);
return v_res_3099_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3100_; 
v___x_3100_ = l_instMonadEIO___redArg();
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(lean_object* v_msg_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v_toApplicative_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3178_; 
v___x_3113_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0);
v___x_3114_ = l_StateRefT_x27_instMonad___redArg(v___x_3113_);
v_toApplicative_3115_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3178_ == 0)
{
lean_object* v_unused_3179_; 
v_unused_3179_ = lean_ctor_get(v___x_3114_, 1);
lean_dec(v_unused_3179_);
v___x_3117_ = v___x_3114_;
v_isShared_3118_ = v_isSharedCheck_3178_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_toApplicative_3115_);
lean_dec(v___x_3114_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3178_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v_toFunctor_3119_; lean_object* v_toSeq_3120_; lean_object* v_toSeqLeft_3121_; lean_object* v_toSeqRight_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3176_; 
v_toFunctor_3119_ = lean_ctor_get(v_toApplicative_3115_, 0);
v_toSeq_3120_ = lean_ctor_get(v_toApplicative_3115_, 2);
v_toSeqLeft_3121_ = lean_ctor_get(v_toApplicative_3115_, 3);
v_toSeqRight_3122_ = lean_ctor_get(v_toApplicative_3115_, 4);
v_isSharedCheck_3176_ = !lean_is_exclusive(v_toApplicative_3115_);
if (v_isSharedCheck_3176_ == 0)
{
lean_object* v_unused_3177_; 
v_unused_3177_ = lean_ctor_get(v_toApplicative_3115_, 1);
lean_dec(v_unused_3177_);
v___x_3124_ = v_toApplicative_3115_;
v_isShared_3125_ = v_isSharedCheck_3176_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_toSeqRight_3122_);
lean_inc(v_toSeqLeft_3121_);
lean_inc(v_toSeq_3120_);
lean_inc(v_toFunctor_3119_);
lean_dec(v_toApplicative_3115_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3176_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___f_3126_; lean_object* v___f_3127_; lean_object* v___f_3128_; lean_object* v___f_3129_; lean_object* v___x_3130_; lean_object* v___f_3131_; lean_object* v___f_3132_; lean_object* v___f_3133_; lean_object* v___x_3135_; 
v___f_3126_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1));
v___f_3127_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2));
lean_inc_ref(v_toFunctor_3119_);
v___f_3128_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3128_, 0, v_toFunctor_3119_);
v___f_3129_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3129_, 0, v_toFunctor_3119_);
v___x_3130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3130_, 0, v___f_3128_);
lean_ctor_set(v___x_3130_, 1, v___f_3129_);
v___f_3131_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3131_, 0, v_toSeqRight_3122_);
v___f_3132_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3132_, 0, v_toSeqLeft_3121_);
v___f_3133_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3133_, 0, v_toSeq_3120_);
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 4, v___f_3131_);
lean_ctor_set(v___x_3124_, 3, v___f_3132_);
lean_ctor_set(v___x_3124_, 2, v___f_3133_);
lean_ctor_set(v___x_3124_, 1, v___f_3126_);
lean_ctor_set(v___x_3124_, 0, v___x_3130_);
v___x_3135_ = v___x_3124_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3130_);
lean_ctor_set(v_reuseFailAlloc_3175_, 1, v___f_3126_);
lean_ctor_set(v_reuseFailAlloc_3175_, 2, v___f_3133_);
lean_ctor_set(v_reuseFailAlloc_3175_, 3, v___f_3132_);
lean_ctor_set(v_reuseFailAlloc_3175_, 4, v___f_3131_);
v___x_3135_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
lean_object* v___x_3137_; 
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 1, v___f_3127_);
lean_ctor_set(v___x_3117_, 0, v___x_3135_);
v___x_3137_ = v___x_3117_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_3135_);
lean_ctor_set(v_reuseFailAlloc_3174_, 1, v___f_3127_);
v___x_3137_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
lean_object* v___x_3138_; lean_object* v_toApplicative_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3172_; 
v___x_3138_ = l_StateRefT_x27_instMonad___redArg(v___x_3137_);
v_toApplicative_3139_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3172_ == 0)
{
lean_object* v_unused_3173_; 
v_unused_3173_ = lean_ctor_get(v___x_3138_, 1);
lean_dec(v_unused_3173_);
v___x_3141_ = v___x_3138_;
v_isShared_3142_ = v_isSharedCheck_3172_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_toApplicative_3139_);
lean_dec(v___x_3138_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3172_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v_toFunctor_3143_; lean_object* v_toSeq_3144_; lean_object* v_toSeqLeft_3145_; lean_object* v_toSeqRight_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3170_; 
v_toFunctor_3143_ = lean_ctor_get(v_toApplicative_3139_, 0);
v_toSeq_3144_ = lean_ctor_get(v_toApplicative_3139_, 2);
v_toSeqLeft_3145_ = lean_ctor_get(v_toApplicative_3139_, 3);
v_toSeqRight_3146_ = lean_ctor_get(v_toApplicative_3139_, 4);
v_isSharedCheck_3170_ = !lean_is_exclusive(v_toApplicative_3139_);
if (v_isSharedCheck_3170_ == 0)
{
lean_object* v_unused_3171_; 
v_unused_3171_ = lean_ctor_get(v_toApplicative_3139_, 1);
lean_dec(v_unused_3171_);
v___x_3148_ = v_toApplicative_3139_;
v_isShared_3149_ = v_isSharedCheck_3170_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_toSeqRight_3146_);
lean_inc(v_toSeqLeft_3145_);
lean_inc(v_toSeq_3144_);
lean_inc(v_toFunctor_3143_);
lean_dec(v_toApplicative_3139_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3170_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___f_3150_; lean_object* v___f_3151_; lean_object* v___f_3152_; lean_object* v___f_3153_; lean_object* v___x_3154_; lean_object* v___f_3155_; lean_object* v___f_3156_; lean_object* v___f_3157_; lean_object* v___x_3159_; 
v___f_3150_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3));
v___f_3151_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4));
lean_inc_ref(v_toFunctor_3143_);
v___f_3152_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3152_, 0, v_toFunctor_3143_);
v___f_3153_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3153_, 0, v_toFunctor_3143_);
v___x_3154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3154_, 0, v___f_3152_);
lean_ctor_set(v___x_3154_, 1, v___f_3153_);
v___f_3155_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3155_, 0, v_toSeqRight_3146_);
v___f_3156_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3156_, 0, v_toSeqLeft_3145_);
v___f_3157_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3157_, 0, v_toSeq_3144_);
if (v_isShared_3149_ == 0)
{
lean_ctor_set(v___x_3148_, 4, v___f_3155_);
lean_ctor_set(v___x_3148_, 3, v___f_3156_);
lean_ctor_set(v___x_3148_, 2, v___f_3157_);
lean_ctor_set(v___x_3148_, 1, v___f_3150_);
lean_ctor_set(v___x_3148_, 0, v___x_3154_);
v___x_3159_ = v___x_3148_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3154_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v___f_3150_);
lean_ctor_set(v_reuseFailAlloc_3169_, 2, v___f_3157_);
lean_ctor_set(v_reuseFailAlloc_3169_, 3, v___f_3156_);
lean_ctor_set(v_reuseFailAlloc_3169_, 4, v___f_3155_);
v___x_3159_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
lean_object* v___x_3161_; 
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 1, v___f_3151_);
lean_ctor_set(v___x_3141_, 0, v___x_3159_);
v___x_3161_ = v___x_3141_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v___x_3159_);
lean_ctor_set(v_reuseFailAlloc_3168_, 1, v___f_3151_);
v___x_3161_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___f_3165_; lean_object* v___x_910__overap_3166_; lean_object* v___x_3167_; 
v___x_3162_ = l_StateRefT_x27_instMonad___redArg(v___x_3161_);
v___x_3163_ = l_Lean_instInhabitedExpr;
v___x_3164_ = l_instInhabitedOfMonad___redArg(v___x_3162_, v___x_3163_);
v___f_3165_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3165_, 0, v___x_3164_);
v___x_910__overap_3166_ = lean_panic_fn_borrowed(v___f_3165_, v_msg_3105_);
lean_dec_ref(v___f_3165_);
lean_inc(v___y_3111_);
lean_inc_ref(v___y_3110_);
lean_inc(v___y_3109_);
lean_inc_ref(v___y_3108_);
lean_inc(v___y_3107_);
lean_inc_ref(v___y_3106_);
v___x_3167_ = lean_apply_7(v___x_910__overap_3166_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, lean_box(0));
return v___x_3167_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___boxed(lean_object* v_msg_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(v_msg_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_3189_, lean_object* v_vals_3190_, lean_object* v_i_3191_, lean_object* v_k_3192_){
_start:
{
lean_object* v___x_3193_; uint8_t v___x_3194_; 
v___x_3193_ = lean_array_get_size(v_keys_3189_);
v___x_3194_ = lean_nat_dec_lt(v_i_3191_, v___x_3193_);
if (v___x_3194_ == 0)
{
lean_object* v___x_3195_; 
lean_dec(v_i_3191_);
v___x_3195_ = lean_box(0);
return v___x_3195_;
}
else
{
lean_object* v_k_x27_3196_; uint8_t v___x_3197_; 
v_k_x27_3196_ = lean_array_fget_borrowed(v_keys_3189_, v_i_3191_);
v___x_3197_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_3192_, v_k_x27_3196_);
if (v___x_3197_ == 0)
{
lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3198_ = lean_unsigned_to_nat(1u);
v___x_3199_ = lean_nat_add(v_i_3191_, v___x_3198_);
lean_dec(v_i_3191_);
v_i_3191_ = v___x_3199_;
goto _start;
}
else
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3201_ = lean_array_fget_borrowed(v_vals_3190_, v_i_3191_);
lean_dec(v_i_3191_);
lean_inc(v___x_3201_);
lean_inc(v_k_x27_3196_);
v___x_3202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3202_, 0, v_k_x27_3196_);
lean_ctor_set(v___x_3202_, 1, v___x_3201_);
v___x_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3202_);
return v___x_3203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_3204_, lean_object* v_vals_3205_, lean_object* v_i_3206_, lean_object* v_k_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_keys_3204_, v_vals_3205_, v_i_3206_, v_k_3207_);
lean_dec_ref(v_k_3207_);
lean_dec_ref(v_vals_3205_);
lean_dec_ref(v_keys_3204_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(lean_object* v_x_3209_, size_t v_x_3210_, lean_object* v_x_3211_){
_start:
{
if (lean_obj_tag(v_x_3209_) == 0)
{
lean_object* v_es_3212_; lean_object* v___x_3213_; size_t v___x_3214_; size_t v___x_3215_; lean_object* v_j_3216_; lean_object* v___x_3217_; 
v_es_3212_ = lean_ctor_get(v_x_3209_, 0);
v___x_3213_ = lean_box(2);
v___x_3214_ = ((size_t)31ULL);
v___x_3215_ = lean_usize_land(v_x_3210_, v___x_3214_);
v_j_3216_ = lean_usize_to_nat(v___x_3215_);
v___x_3217_ = lean_array_get_borrowed(v___x_3213_, v_es_3212_, v_j_3216_);
lean_dec(v_j_3216_);
switch(lean_obj_tag(v___x_3217_))
{
case 0:
{
lean_object* v_key_3218_; lean_object* v_val_3219_; uint8_t v___x_3220_; 
v_key_3218_ = lean_ctor_get(v___x_3217_, 0);
v_val_3219_ = lean_ctor_get(v___x_3217_, 1);
v___x_3220_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_3211_, v_key_3218_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; 
v___x_3221_ = lean_box(0);
return v___x_3221_;
}
else
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
lean_inc(v_val_3219_);
lean_inc(v_key_3218_);
v___x_3222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3222_, 0, v_key_3218_);
lean_ctor_set(v___x_3222_, 1, v_val_3219_);
v___x_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
return v___x_3223_;
}
}
case 1:
{
lean_object* v_node_3224_; size_t v___x_3225_; size_t v___x_3226_; 
v_node_3224_ = lean_ctor_get(v___x_3217_, 0);
v___x_3225_ = ((size_t)5ULL);
v___x_3226_ = lean_usize_shift_right(v_x_3210_, v___x_3225_);
v_x_3209_ = v_node_3224_;
v_x_3210_ = v___x_3226_;
goto _start;
}
default: 
{
lean_object* v___x_3228_; 
v___x_3228_ = lean_box(0);
return v___x_3228_;
}
}
}
else
{
lean_object* v_ks_3229_; lean_object* v_vs_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v_ks_3229_ = lean_ctor_get(v_x_3209_, 0);
v_vs_3230_ = lean_ctor_get(v_x_3209_, 1);
v___x_3231_ = lean_unsigned_to_nat(0u);
v___x_3232_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_ks_3229_, v_vs_3230_, v___x_3231_, v_x_3211_);
return v___x_3232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg___boxed(lean_object* v_x_3233_, lean_object* v_x_3234_, lean_object* v_x_3235_){
_start:
{
size_t v_x_1232__boxed_3236_; lean_object* v_res_3237_; 
v_x_1232__boxed_3236_ = lean_unbox_usize(v_x_3234_);
lean_dec(v_x_3234_);
v_res_3237_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3233_, v_x_1232__boxed_3236_, v_x_3235_);
lean_dec_ref(v_x_3235_);
lean_dec_ref(v_x_3233_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(lean_object* v_x_3238_, lean_object* v_x_3239_){
_start:
{
uint64_t v___x_3240_; size_t v___x_3241_; lean_object* v___x_3242_; 
v___x_3240_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_3239_);
v___x_3241_ = lean_uint64_to_usize(v___x_3240_);
v___x_3242_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3238_, v___x_3241_, v_x_3239_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg___boxed(lean_object* v_x_3243_, lean_object* v_x_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v_x_3243_, v_x_3244_);
lean_dec_ref(v_x_3244_);
lean_dec_ref(v_x_3243_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0(lean_object* v_e_3246_, lean_object* v_cache_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
lean_object* v___x_3250_; 
v___x_3250_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v___y_3249_, v_e_3246_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3251_, 0, v_cache_3247_);
lean_ctor_set(v___x_3251_, 1, v___y_3249_);
v___x_3252_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_3246_, v___y_3248_, v___x_3251_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3262_; 
v_a_3253_ = lean_ctor_get(v___x_3252_, 1);
v_a_3254_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3256_ = v___x_3252_;
v_isShared_3257_ = v_isSharedCheck_3262_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3253_);
lean_inc(v_a_3254_);
lean_dec(v___x_3252_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3262_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v_set_3258_; lean_object* v___x_3260_; 
v_set_3258_ = lean_ctor_get(v_a_3253_, 1);
lean_inc_ref(v_set_3258_);
lean_dec(v_a_3253_);
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 1, v_set_3258_);
v___x_3260_ = v___x_3256_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3254_);
lean_ctor_set(v_reuseFailAlloc_3261_, 1, v_set_3258_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
else
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3272_; 
v_a_3263_ = lean_ctor_get(v___x_3252_, 1);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3272_ == 0)
{
lean_object* v_unused_3273_; 
v_unused_3273_ = lean_ctor_get(v___x_3252_, 0);
lean_dec(v_unused_3273_);
v___x_3265_ = v___x_3252_;
v_isShared_3266_ = v_isSharedCheck_3272_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3252_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3272_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v_map_3267_; lean_object* v_set_3268_; lean_object* v___x_3270_; 
v_map_3267_ = lean_ctor_get(v_a_3263_, 0);
lean_inc_ref(v_map_3267_);
v_set_3268_ = lean_ctor_get(v_a_3263_, 1);
lean_inc_ref(v_set_3268_);
lean_dec(v_a_3263_);
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 1, v_set_3268_);
lean_ctor_set(v___x_3265_, 0, v_map_3267_);
v___x_3270_ = v___x_3265_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_map_3267_);
lean_ctor_set(v_reuseFailAlloc_3271_, 1, v_set_3268_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
}
else
{
lean_object* v_val_3274_; lean_object* v_fst_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3282_; 
lean_dec_ref(v_cache_3247_);
lean_dec_ref(v_e_3246_);
v_val_3274_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_val_3274_);
lean_dec_ref_known(v___x_3250_, 1);
v_fst_3275_ = lean_ctor_get(v_val_3274_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v_val_3274_);
if (v_isSharedCheck_3282_ == 0)
{
lean_object* v_unused_3283_; 
v_unused_3283_ = lean_ctor_get(v_val_3274_, 1);
lean_dec(v_unused_3283_);
v___x_3277_ = v_val_3274_;
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_fst_3275_);
lean_dec(v_val_3274_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3280_; 
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 1, v___y_3249_);
v___x_3280_ = v___x_3277_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_fst_3275_);
lean_ctor_set(v_reuseFailAlloc_3281_, 1, v___y_3249_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0___boxed(lean_object* v_e_3284_, lean_object* v_cache_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v_res_3288_; 
v_res_3288_ = l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0(v_e_3284_, v_cache_3285_, v___y_3286_, v___y_3287_);
lean_dec_ref(v___y_3286_);
return v_res_3288_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1(void){
_start:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3290_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__4));
v___x_3291_ = lean_unsigned_to_nat(16u);
v___x_3292_ = lean_unsigned_to_nat(399u);
v___x_3293_ = ((lean_object*)(l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__0));
v___x_3294_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__2));
v___x_3295_ = l_mkPanicMessageWithDecl(v___x_3294_, v___x_3293_, v___x_3292_, v___x_3291_, v___x_3290_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks(lean_object* v_e_3296_, lean_object* v_cache_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_){
_start:
{
lean_object* v___f_3305_; lean_object* v___x_3306_; lean_object* v_env_3307_; uint8_t v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3321_; 
v___f_3305_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3305_, 0, v_e_3296_);
lean_closure_set(v___f_3305_, 1, v_cache_3297_);
v___x_3306_ = lean_st_ref_get(v_a_3303_);
v_env_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc_ref(v_env_3307_);
lean_dec(v___x_3306_);
v___x_3308_ = 0;
v___x_3309_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3309_, 0, v_env_3307_);
lean_ctor_set_uint8(v___x_3309_, sizeof(void*)*1, v___x_3308_);
lean_ctor_set_uint8(v___x_3309_, sizeof(void*)*1 + 1, v___x_3308_);
v___x_3310_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3305_, v___x_3309_, v_a_3299_);
v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3313_ = v___x_3310_;
v_isShared_3314_ = v_isSharedCheck_3321_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3310_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3321_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
if (lean_obj_tag(v_a_3311_) == 0)
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
lean_dec_ref_known(v_a_3311_, 1);
lean_del_object(v___x_3313_);
v___x_3315_ = lean_obj_once(&l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1, &l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1_once, _init_l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1);
v___x_3316_ = l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(v___x_3315_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_);
return v___x_3316_;
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; 
v_a_3317_ = lean_ctor_get(v_a_3311_, 0);
lean_inc(v_a_3317_);
lean_dec_ref_known(v_a_3311_, 1);
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 0, v_a_3317_);
v___x_3319_ = v___x_3313_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3317_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___boxed(lean_object* v_e_3322_, lean_object* v_cache_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_Lean_Meta_Sym_shareCommonWithoutChecks(v_e_3322_, v_cache_3323_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_);
lean_dec(v_a_3329_);
lean_dec_ref(v_a_3328_);
lean_dec(v_a_3327_);
lean_dec_ref(v_a_3326_);
lean_dec(v_a_3325_);
lean_dec_ref(v_a_3324_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0(lean_object* v_00_u03b2_3332_, lean_object* v_x_3333_, lean_object* v_x_3334_){
_start:
{
lean_object* v___x_3335_; 
v___x_3335_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v_x_3333_, v_x_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___boxed(lean_object* v_00_u03b2_3336_, lean_object* v_x_3337_, lean_object* v_x_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0(v_00_u03b2_3336_, v_x_3337_, v_x_3338_);
lean_dec_ref(v_x_3338_);
lean_dec_ref(v_x_3337_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0(lean_object* v_00_u03b2_3340_, lean_object* v_x_3341_, size_t v_x_3342_, lean_object* v_x_3343_){
_start:
{
lean_object* v___x_3344_; 
v___x_3344_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3341_, v_x_3342_, v_x_3343_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3345_, lean_object* v_x_3346_, lean_object* v_x_3347_, lean_object* v_x_3348_){
_start:
{
size_t v_x_1437__boxed_3349_; lean_object* v_res_3350_; 
v_x_1437__boxed_3349_ = lean_unbox_usize(v_x_3347_);
lean_dec(v_x_3347_);
v_res_3350_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0(v_00_u03b2_3345_, v_x_3346_, v_x_1437__boxed_3349_, v_x_3348_);
lean_dec_ref(v_x_3348_);
lean_dec_ref(v_x_3346_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3351_, lean_object* v_keys_3352_, lean_object* v_vals_3353_, lean_object* v_heq_3354_, lean_object* v_i_3355_, lean_object* v_k_3356_){
_start:
{
lean_object* v___x_3357_; 
v___x_3357_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_keys_3352_, v_vals_3353_, v_i_3355_, v_k_3356_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3358_, lean_object* v_keys_3359_, lean_object* v_vals_3360_, lean_object* v_heq_3361_, lean_object* v_i_3362_, lean_object* v_k_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2(v_00_u03b2_3358_, v_keys_3359_, v_vals_3360_, v_heq_3361_, v_i_3362_, v_k_3363_);
lean_dec_ref(v_k_3363_);
lean_dec_ref(v_vals_3360_);
lean_dec_ref(v_keys_3359_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(lean_object* v_msg_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v_ref_3371_; lean_object* v___x_3372_; lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3381_; 
v_ref_3371_ = lean_ctor_get(v___y_3368_, 2);
v___x_3372_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3375_ = v___x_3372_;
v_isShared_3376_ = v_isSharedCheck_3381_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3372_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3381_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3377_; lean_object* v___x_3379_; 
lean_inc(v_ref_3371_);
v___x_3377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3377_, 0, v_ref_3371_);
lean_ctor_set(v___x_3377_, 1, v_a_3373_);
if (v_isShared_3376_ == 0)
{
lean_ctor_set_tag(v___x_3375_, 1);
lean_ctor_set(v___x_3375_, 0, v___x_3377_);
v___x_3379_ = v___x_3375_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3377_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg___boxed(lean_object* v_msg_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v_msg_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
return v_res_3388_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1(void){
_start:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3390_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__0));
v___x_3391_ = l_Lean_stringToMessageData(v___x_3390_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(lean_object* v_e_3392_, lean_object* v_cache_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_){
_start:
{
lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; uint8_t v___x_3411_; 
v___x_3411_ = l_Lean_Expr_hasLooseBVars(v_e_3392_);
if (v___x_3411_ == 0)
{
v___y_3402_ = v_a_3394_;
v___y_3403_ = v_a_3395_;
v___y_3404_ = v_a_3396_;
v___y_3405_ = v_a_3397_;
v___y_3406_ = v_a_3398_;
v___y_3407_ = v_a_3399_;
goto v___jp_3401_;
}
else
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
lean_dec_ref(v_cache_3393_);
v___x_3412_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1);
v___x_3413_ = l_Lean_indentExpr(v_e_3392_);
v___x_3414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3412_);
lean_ctor_set(v___x_3414_, 1, v___x_3413_);
v___x_3415_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v___x_3414_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3418_ = v___x_3415_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3415_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3416_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
v___jp_3401_:
{
lean_object* v___x_3408_; 
v___x_3408_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3392_, v___y_3402_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v___x_3410_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc(v_a_3409_);
lean_dec_ref_known(v___x_3408_, 1);
v___x_3410_ = l_Lean_Meta_Sym_shareCommonWithoutChecks(v_a_3409_, v_cache_3393_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_);
return v___x_3410_;
}
else
{
lean_dec_ref(v_cache_3393_);
return v___x_3408_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___boxed(lean_object* v_e_3424_, lean_object* v_cache_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3424_, v_cache_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec(v_a_3427_);
lean_dec_ref(v_a_3426_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0(lean_object* v_00_u03b1_3434_, lean_object* v_msg_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v___x_3443_; 
v___x_3443_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v_msg_3435_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___boxed(lean_object* v_00_u03b1_3444_, lean_object* v_msg_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
lean_object* v_res_3453_; 
v_res_3453_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0(v_00_u03b1_3444_, v_msg_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___lam__0(lean_object* v_e_3454_, lean_object* v___x_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v___y_3457_, v_e_3454_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3455_);
lean_ctor_set(v___x_3459_, 1, v___y_3457_);
v___x_3460_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_3454_, v___y_3456_, v___x_3459_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3470_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 1);
v_a_3462_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3464_ = v___x_3460_;
v_isShared_3465_ = v_isSharedCheck_3470_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3461_);
lean_inc(v_a_3462_);
lean_dec(v___x_3460_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3470_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v_set_3466_; lean_object* v___x_3468_; 
v_set_3466_ = lean_ctor_get(v_a_3461_, 1);
lean_inc_ref(v_set_3466_);
lean_dec(v_a_3461_);
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 1, v_set_3466_);
v___x_3468_ = v___x_3464_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3462_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_set_3466_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3480_; 
v_a_3471_ = lean_ctor_get(v___x_3460_, 1);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3480_ == 0)
{
lean_object* v_unused_3481_; 
v_unused_3481_ = lean_ctor_get(v___x_3460_, 0);
lean_dec(v_unused_3481_);
v___x_3473_ = v___x_3460_;
v_isShared_3474_ = v_isSharedCheck_3480_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3460_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3480_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v_map_3475_; lean_object* v_set_3476_; lean_object* v___x_3478_; 
v_map_3475_ = lean_ctor_get(v_a_3471_, 0);
lean_inc_ref(v_map_3475_);
v_set_3476_ = lean_ctor_get(v_a_3471_, 1);
lean_inc_ref(v_set_3476_);
lean_dec(v_a_3471_);
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 1, v_set_3476_);
lean_ctor_set(v___x_3473_, 0, v_map_3475_);
v___x_3478_ = v___x_3473_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_map_3475_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_set_3476_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
else
{
lean_object* v_val_3482_; lean_object* v_fst_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_dec_ref(v___x_3455_);
lean_dec_ref(v_e_3454_);
v_val_3482_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_val_3482_);
lean_dec_ref_known(v___x_3458_, 1);
v_fst_3483_ = lean_ctor_get(v_val_3482_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v_val_3482_);
if (v_isSharedCheck_3490_ == 0)
{
lean_object* v_unused_3491_; 
v_unused_3491_ = lean_ctor_get(v_val_3482_, 1);
lean_dec(v_unused_3491_);
v___x_3485_ = v_val_3482_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_fst_3483_);
lean_dec(v_val_3482_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 1, v___y_3457_);
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_fst_3483_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v___y_3457_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___lam__0___boxed(lean_object* v_e_3492_, lean_object* v___x_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
lean_object* v_res_3496_; 
v_res_3496_ = l_Lean_Meta_Sym_shareCommon___lam__0(v_e_3492_, v___x_3493_, v___y_3494_, v___y_3495_);
lean_dec_ref(v___y_3494_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon(lean_object* v_e_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_){
_start:
{
lean_object* v___x_3505_; lean_object* v_a_3506_; lean_object* v___x_3507_; lean_object* v___f_3508_; lean_object* v___x_3509_; lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3520_; 
v___x_3505_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3498_, v_a_3503_);
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3506_);
lean_dec_ref(v___x_3505_);
v___x_3507_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
lean_inc_ref(v_e_3497_);
v___f_3508_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommon___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3508_, 0, v_e_3497_);
lean_closure_set(v___f_3508_, 1, v___x_3507_);
v___x_3509_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3508_, v_a_3506_, v_a_3499_);
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3512_ = v___x_3509_;
v_isShared_3513_ = v_isSharedCheck_3520_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3509_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3520_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
if (lean_obj_tag(v_a_3510_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3515_; 
lean_del_object(v___x_3512_);
v_a_3514_ = lean_ctor_get(v_a_3510_, 0);
lean_inc(v_a_3514_);
lean_dec_ref_known(v_a_3510_, 1);
v___x_3515_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3497_, v_a_3514_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_);
return v___x_3515_;
}
else
{
lean_object* v_a_3516_; lean_object* v___x_3518_; 
lean_dec_ref(v_e_3497_);
v_a_3516_ = lean_ctor_get(v_a_3510_, 0);
lean_inc(v_a_3516_);
lean_dec_ref_known(v_a_3510_, 1);
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 0, v_a_3516_);
v___x_3518_ = v___x_3512_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_a_3516_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___boxed(lean_object* v_e_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_){
_start:
{
lean_object* v_res_3529_; 
v_res_3529_ = l_Lean_Meta_Sym_shareCommon(v_e_3521_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_);
lean_dec(v_a_3527_);
lean_dec_ref(v_a_3526_);
lean_dec(v_a_3525_);
lean_dec_ref(v_a_3524_);
lean_dec(v_a_3523_);
lean_dec_ref(v_a_3522_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___lam__0(lean_object* v_e_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_3530_, v___y_3531_, v___y_3532_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___lam__0___boxed(lean_object* v_e_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l_Lean_Meta_Sym_shareCommonInc___lam__0(v_e_3534_, v___y_3535_, v___y_3536_);
lean_dec_ref(v___y_3535_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object* v_e_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_){
_start:
{
lean_object* v___f_3546_; lean_object* v___x_3547_; lean_object* v_a_3548_; lean_object* v___x_3549_; lean_object* v_a_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3560_; 
lean_inc_ref(v_e_3538_);
v___f_3546_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommonInc___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3546_, 0, v_e_3538_);
v___x_3547_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3539_, v_a_3544_);
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3548_);
lean_dec_ref(v___x_3547_);
v___x_3549_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3546_, v_a_3548_, v_a_3540_);
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3552_ = v___x_3549_;
v_isShared_3553_ = v_isSharedCheck_3560_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_a_3550_);
lean_dec(v___x_3549_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3560_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
if (lean_obj_tag(v_a_3550_) == 0)
{
lean_object* v___x_3554_; lean_object* v___x_3555_; 
lean_dec_ref_known(v_a_3550_, 1);
lean_del_object(v___x_3552_);
v___x_3554_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
v___x_3555_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3538_, v___x_3554_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_);
return v___x_3555_;
}
else
{
lean_object* v_a_3556_; lean_object* v___x_3558_; 
lean_dec_ref(v_e_3538_);
v_a_3556_ = lean_ctor_get(v_a_3550_, 0);
lean_inc(v_a_3556_);
lean_dec_ref_known(v_a_3550_, 1);
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 0, v_a_3556_);
v___x_3558_ = v___x_3552_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3556_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___boxed(lean_object* v_e_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l_Lean_Meta_Sym_shareCommonInc(v_e_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share(lean_object* v_e_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_){
_start:
{
lean_object* v___x_3578_; 
v___x_3578_ = l_Lean_Meta_Sym_shareCommonInc(v_e_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_);
return v___x_3578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___boxed(lean_object* v_e_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = l_Lean_Meta_Sym_share(v_e_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_);
lean_dec(v_a_3585_);
lean_dec_ref(v_a_3584_);
lean_dec(v_a_3583_);
lean_dec_ref(v_a_3582_);
lean_dec(v_a_3581_);
lean_dec_ref(v_a_3580_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg(lean_object* v_a_3588_){
_start:
{
lean_object* v___x_3590_; uint8_t v_debug_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3590_ = lean_st_ref_get(v_a_3588_);
v_debug_3591_ = lean_ctor_get_uint8(v___x_3590_, sizeof(void*)*12);
lean_dec(v___x_3590_);
v___x_3592_ = lean_box(v_debug_3591_);
v___x_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3592_);
return v___x_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg___boxed(lean_object* v_a_3594_, lean_object* v_a_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l_Lean_Meta_Sym_isDebugEnabled___redArg(v_a_3594_);
lean_dec(v_a_3594_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled(lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_){
_start:
{
lean_object* v___x_3604_; uint8_t v_debug_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3604_ = lean_st_ref_get(v_a_3598_);
v_debug_3605_ = lean_ctor_get_uint8(v___x_3604_, sizeof(void*)*12);
lean_dec(v___x_3604_);
v___x_3606_ = lean_box(v_debug_3605_);
v___x_3607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3606_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___boxed(lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l_Lean_Meta_Sym_isDebugEnabled(v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_);
lean_dec(v_a_3613_);
lean_dec_ref(v_a_3612_);
lean_dec(v_a_3611_);
lean_dec_ref(v_a_3610_);
lean_dec(v_a_3609_);
lean_dec_ref(v_a_3608_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object* v_a_3616_){
_start:
{
lean_object* v_config_3618_; lean_object* v___x_3619_; 
v_config_3618_ = lean_ctor_get(v_a_3616_, 1);
lean_inc_ref(v_config_3618_);
v___x_3619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3619_, 0, v_config_3618_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg___boxed(lean_object* v_a_3620_, lean_object* v_a_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3620_);
lean_dec_ref(v_a_3620_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig(lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_){
_start:
{
lean_object* v___x_3630_; 
v___x_3630_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3623_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___boxed(lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l_Lean_Meta_Sym_getConfig(v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_);
lean_dec(v_a_3636_);
lean_dec_ref(v_a_3635_);
lean_dec(v_a_3634_);
lean_dec_ref(v_a_3633_);
lean_dec(v_a_3632_);
lean_dec_ref(v_a_3631_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(lean_object* v_cls_3639_, lean_object* v_msg_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v_ref_3646_; lean_object* v___x_3647_; lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3693_; 
v_ref_3646_ = lean_ctor_get(v___y_3643_, 2);
v___x_3647_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
v_a_3648_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3650_ = v___x_3647_;
v_isShared_3651_ = v_isSharedCheck_3693_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v___x_3647_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3693_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3652_; lean_object* v_traceState_3653_; lean_object* v_env_3654_; lean_object* v_nextMacroScope_3655_; lean_object* v_ngen_3656_; lean_object* v_auxDeclNGen_3657_; lean_object* v_cache_3658_; lean_object* v_recordedDeps_3659_; lean_object* v_messages_3660_; lean_object* v_infoState_3661_; lean_object* v_snapshotTasks_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3692_; 
v___x_3652_ = lean_st_ref_take(v___y_3644_);
v_traceState_3653_ = lean_ctor_get(v___x_3652_, 4);
v_env_3654_ = lean_ctor_get(v___x_3652_, 0);
v_nextMacroScope_3655_ = lean_ctor_get(v___x_3652_, 1);
v_ngen_3656_ = lean_ctor_get(v___x_3652_, 2);
v_auxDeclNGen_3657_ = lean_ctor_get(v___x_3652_, 3);
v_cache_3658_ = lean_ctor_get(v___x_3652_, 5);
v_recordedDeps_3659_ = lean_ctor_get(v___x_3652_, 6);
v_messages_3660_ = lean_ctor_get(v___x_3652_, 7);
v_infoState_3661_ = lean_ctor_get(v___x_3652_, 8);
v_snapshotTasks_3662_ = lean_ctor_get(v___x_3652_, 9);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3664_ = v___x_3652_;
v_isShared_3665_ = v_isSharedCheck_3692_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_snapshotTasks_3662_);
lean_inc(v_infoState_3661_);
lean_inc(v_messages_3660_);
lean_inc(v_recordedDeps_3659_);
lean_inc(v_cache_3658_);
lean_inc(v_traceState_3653_);
lean_inc(v_auxDeclNGen_3657_);
lean_inc(v_ngen_3656_);
lean_inc(v_nextMacroScope_3655_);
lean_inc(v_env_3654_);
lean_dec(v___x_3652_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3692_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
uint64_t v_tid_3666_; lean_object* v_traces_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3691_; 
v_tid_3666_ = lean_ctor_get_uint64(v_traceState_3653_, sizeof(void*)*1);
v_traces_3667_ = lean_ctor_get(v_traceState_3653_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v_traceState_3653_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3669_ = v_traceState_3653_;
v_isShared_3670_ = v_isSharedCheck_3691_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_traces_3667_);
lean_dec(v_traceState_3653_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3691_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; double v___x_3673_; uint8_t v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3682_; 
v___x_3671_ = lean_box(0);
v___x_3672_ = lean_box(0);
v___x_3673_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_3674_ = 0;
v___x_3675_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_3676_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3676_, 0, v_cls_3639_);
lean_ctor_set(v___x_3676_, 1, v___x_3672_);
lean_ctor_set(v___x_3676_, 2, v___x_3675_);
lean_ctor_set_float(v___x_3676_, sizeof(void*)*3, v___x_3673_);
lean_ctor_set_float(v___x_3676_, sizeof(void*)*3 + 8, v___x_3673_);
lean_ctor_set_uint8(v___x_3676_, sizeof(void*)*3 + 16, v___x_3674_);
v___x_3677_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
v___x_3678_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3676_);
lean_ctor_set(v___x_3678_, 1, v_a_3648_);
lean_ctor_set(v___x_3678_, 2, v___x_3677_);
lean_inc(v_ref_3646_);
v___x_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3679_, 0, v_ref_3646_);
lean_ctor_set(v___x_3679_, 1, v___x_3678_);
v___x_3680_ = l_Lean_PersistentArray_push___redArg(v_traces_3667_, v___x_3679_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v___x_3680_);
v___x_3682_ = v___x_3669_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3680_);
lean_ctor_set_uint64(v_reuseFailAlloc_3690_, sizeof(void*)*1, v_tid_3666_);
v___x_3682_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
lean_object* v___x_3684_; 
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 4, v___x_3682_);
v___x_3684_ = v___x_3664_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_env_3654_);
lean_ctor_set(v_reuseFailAlloc_3689_, 1, v_nextMacroScope_3655_);
lean_ctor_set(v_reuseFailAlloc_3689_, 2, v_ngen_3656_);
lean_ctor_set(v_reuseFailAlloc_3689_, 3, v_auxDeclNGen_3657_);
lean_ctor_set(v_reuseFailAlloc_3689_, 4, v___x_3682_);
lean_ctor_set(v_reuseFailAlloc_3689_, 5, v_cache_3658_);
lean_ctor_set(v_reuseFailAlloc_3689_, 6, v_recordedDeps_3659_);
lean_ctor_set(v_reuseFailAlloc_3689_, 7, v_messages_3660_);
lean_ctor_set(v_reuseFailAlloc_3689_, 8, v_infoState_3661_);
lean_ctor_set(v_reuseFailAlloc_3689_, 9, v_snapshotTasks_3662_);
v___x_3684_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
lean_object* v___x_3685_; lean_object* v___x_3687_; 
v___x_3685_ = lean_st_ref_put(v___y_3644_, v___x_3684_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 0, v___x_3671_);
v___x_3687_ = v___x_3650_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3671_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg___boxed(lean_object* v_cls_3694_, lean_object* v_msg_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v_cls_3694_, v_msg_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
return v_res_3701_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_reportIssue___closed__2(void){
_start:
{
lean_object* v___x_3705_; uint8_t v___x_3706_; double v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3705_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_3706_ = 1;
v___x_3707_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_3708_ = lean_box(0);
v___x_3709_ = ((lean_object*)(l_Lean_Meta_Sym_reportIssue___closed__1));
v___x_3710_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3710_, 0, v___x_3709_);
lean_ctor_set(v___x_3710_, 1, v___x_3708_);
lean_ctor_set(v___x_3710_, 2, v___x_3705_);
lean_ctor_set_float(v___x_3710_, sizeof(void*)*3, v___x_3707_);
lean_ctor_set_float(v___x_3710_, sizeof(void*)*3 + 8, v___x_3707_);
lean_ctor_set_uint8(v___x_3710_, sizeof(void*)*3 + 16, v___x_3706_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue(lean_object* v_msg_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_){
_start:
{
lean_object* v___x_3722_; lean_object* v_a_3723_; lean_object* v___x_3724_; lean_object* v_share_3725_; lean_object* v_maxFVar_3726_; lean_object* v_proofInstInfo_3727_; lean_object* v_proofInstInfoFVar_3728_; lean_object* v_inferType_3729_; lean_object* v_getLevel_3730_; lean_object* v_congrInfo_3731_; lean_object* v_defEqI_3732_; lean_object* v_extensions_3733_; lean_object* v_issues_3734_; lean_object* v_canon_3735_; lean_object* v_instanceOverrides_3736_; uint8_t v_debug_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3757_; 
v___x_3722_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3711_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_);
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref(v___x_3722_);
v___x_3724_ = lean_st_ref_take(v_a_3713_);
v_share_3725_ = lean_ctor_get(v___x_3724_, 0);
v_maxFVar_3726_ = lean_ctor_get(v___x_3724_, 1);
v_proofInstInfo_3727_ = lean_ctor_get(v___x_3724_, 2);
v_proofInstInfoFVar_3728_ = lean_ctor_get(v___x_3724_, 3);
v_inferType_3729_ = lean_ctor_get(v___x_3724_, 4);
v_getLevel_3730_ = lean_ctor_get(v___x_3724_, 5);
v_congrInfo_3731_ = lean_ctor_get(v___x_3724_, 6);
v_defEqI_3732_ = lean_ctor_get(v___x_3724_, 7);
v_extensions_3733_ = lean_ctor_get(v___x_3724_, 8);
v_issues_3734_ = lean_ctor_get(v___x_3724_, 9);
v_canon_3735_ = lean_ctor_get(v___x_3724_, 10);
v_instanceOverrides_3736_ = lean_ctor_get(v___x_3724_, 11);
v_debug_3737_ = lean_ctor_get_uint8(v___x_3724_, sizeof(void*)*12);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3739_ = v___x_3724_;
v_isShared_3740_ = v_isSharedCheck_3757_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_instanceOverrides_3736_);
lean_inc(v_canon_3735_);
lean_inc(v_issues_3734_);
lean_inc(v_extensions_3733_);
lean_inc(v_defEqI_3732_);
lean_inc(v_congrInfo_3731_);
lean_inc(v_getLevel_3730_);
lean_inc(v_inferType_3729_);
lean_inc(v_proofInstInfoFVar_3728_);
lean_inc(v_proofInstInfo_3727_);
lean_inc(v_maxFVar_3726_);
lean_inc(v_share_3725_);
lean_dec(v___x_3724_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3757_;
goto v_resetjp_3738_;
}
v___jp_3719_:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3720_ = lean_box(0);
v___x_3721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3720_);
return v___x_3721_;
}
v_resetjp_3738_:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3746_; 
v___x_3741_ = lean_obj_once(&l_Lean_Meta_Sym_reportIssue___closed__2, &l_Lean_Meta_Sym_reportIssue___closed__2_once, _init_l_Lean_Meta_Sym_reportIssue___closed__2);
v___x_3742_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
lean_inc(v_a_3723_);
v___x_3743_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3741_);
lean_ctor_set(v___x_3743_, 1, v_a_3723_);
lean_ctor_set(v___x_3743_, 2, v___x_3742_);
v___x_3744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3743_);
lean_ctor_set(v___x_3744_, 1, v_issues_3734_);
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 9, v___x_3744_);
v___x_3746_ = v___x_3739_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_share_3725_);
lean_ctor_set(v_reuseFailAlloc_3756_, 1, v_maxFVar_3726_);
lean_ctor_set(v_reuseFailAlloc_3756_, 2, v_proofInstInfo_3727_);
lean_ctor_set(v_reuseFailAlloc_3756_, 3, v_proofInstInfoFVar_3728_);
lean_ctor_set(v_reuseFailAlloc_3756_, 4, v_inferType_3729_);
lean_ctor_set(v_reuseFailAlloc_3756_, 5, v_getLevel_3730_);
lean_ctor_set(v_reuseFailAlloc_3756_, 6, v_congrInfo_3731_);
lean_ctor_set(v_reuseFailAlloc_3756_, 7, v_defEqI_3732_);
lean_ctor_set(v_reuseFailAlloc_3756_, 8, v_extensions_3733_);
lean_ctor_set(v_reuseFailAlloc_3756_, 9, v___x_3744_);
lean_ctor_set(v_reuseFailAlloc_3756_, 10, v_canon_3735_);
lean_ctor_set(v_reuseFailAlloc_3756_, 11, v_instanceOverrides_3736_);
lean_ctor_set_uint8(v_reuseFailAlloc_3756_, sizeof(void*)*12, v_debug_3737_);
v___x_3746_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
lean_object* v___x_3747_; lean_object* v_toCold_3748_; lean_object* v_options_3749_; uint8_t v_hasTrace_3750_; 
v___x_3747_ = lean_st_ref_put(v_a_3713_, v___x_3746_);
v_toCold_3748_ = lean_ctor_get(v_a_3716_, 0);
v_options_3749_ = lean_ctor_get(v_toCold_3748_, 2);
v_hasTrace_3750_ = lean_ctor_get_uint8(v_options_3749_, sizeof(void*)*1);
if (v_hasTrace_3750_ == 0)
{
lean_dec(v_a_3723_);
goto v___jp_3719_;
}
else
{
lean_object* v_inheritedTraceOptions_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; uint8_t v___x_3754_; 
v_inheritedTraceOptions_3751_ = lean_ctor_get(v_toCold_3748_, 11);
v___x_3752_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_3753_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__2);
v___x_3754_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3751_, v_options_3749_, v___x_3753_);
if (v___x_3754_ == 0)
{
lean_dec(v_a_3723_);
goto v___jp_3719_;
}
else
{
lean_object* v___x_3755_; 
v___x_3755_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v___x_3752_, v_a_3723_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_);
return v___x_3755_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue___boxed(lean_object* v_msg_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_){
_start:
{
lean_object* v_res_3766_; 
v_res_3766_ = l_Lean_Meta_Sym_reportIssue(v_msg_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_);
lean_dec(v_a_3764_);
lean_dec_ref(v_a_3763_);
lean_dec(v_a_3762_);
lean_dec_ref(v_a_3761_);
lean_dec(v_a_3760_);
lean_dec_ref(v_a_3759_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0(lean_object* v_cls_3767_, lean_object* v_msg_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
lean_object* v___x_3776_; 
v___x_3776_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v_cls_3767_, v_msg_3768_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_);
return v___x_3776_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___boxed(lean_object* v_cls_3777_, lean_object* v_msg_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
lean_object* v_res_3786_; 
v_res_3786_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0(v_cls_3777_, v_msg_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose(lean_object* v_msg_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_){
_start:
{
lean_object* v___x_3795_; lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3806_; 
v___x_3795_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3788_);
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3798_ = v___x_3795_;
v_isShared_3799_ = v_isSharedCheck_3806_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v___x_3795_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3806_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
uint8_t v_verbose_3800_; 
v_verbose_3800_ = lean_ctor_get_uint8(v_a_3796_, 0);
lean_dec(v_a_3796_);
if (v_verbose_3800_ == 0)
{
lean_object* v___x_3801_; lean_object* v___x_3803_; 
lean_dec_ref(v_msg_3787_);
v___x_3801_ = lean_box(0);
if (v_isShared_3799_ == 0)
{
lean_ctor_set(v___x_3798_, 0, v___x_3801_);
v___x_3803_ = v___x_3798_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v___x_3801_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
else
{
lean_object* v___x_3805_; 
lean_del_object(v___x_3798_);
v___x_3805_ = l_Lean_Meta_Sym_reportIssue(v_msg_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_);
return v___x_3805_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose___boxed(lean_object* v_msg_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l_Lean_Meta_Sym_reportIssueIfVerbose(v_msg_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_);
lean_dec(v_a_3813_);
lean_dec_ref(v_a_3812_);
lean_dec(v_a_3811_);
lean_dec_ref(v_a_3810_);
lean_dec(v_a_3809_);
lean_dec_ref(v_a_3808_);
return v_res_3815_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7(void){
_start:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3831_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6));
v___x_3832_ = l_String_toRawSubstring_x27(v___x_3831_);
return v___x_3832_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24(void){
_start:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3870_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_3871_ = l_String_toRawSubstring_x27(v___x_3870_);
return v___x_3871_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30(void){
_start:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3883_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29));
v___x_3884_ = l_String_toRawSubstring_x27(v___x_3883_);
return v___x_3884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(lean_object* v_s_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_){
_start:
{
lean_object* v_msg_3911_; lean_object* v_quotContext_3912_; lean_object* v_currMacroScope_3913_; lean_object* v_ref_3914_; lean_object* v___y_3915_; lean_object* v___x_3930_; lean_object* v___x_3931_; uint8_t v___x_3932_; 
lean_inc(v_s_3907_);
v___x_3930_ = l_Lean_Syntax_getKind(v_s_3907_);
v___x_3931_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16));
v___x_3932_ = lean_name_eq(v___x_3930_, v___x_3931_);
lean_dec(v___x_3930_);
if (v___x_3932_ == 0)
{
lean_object* v_quotContext_3933_; lean_object* v_currMacroScope_3934_; lean_object* v_ref_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v_quotContext_3933_ = lean_ctor_get(v_a_3908_, 1);
v_currMacroScope_3934_ = lean_ctor_get(v_a_3908_, 2);
v_ref_3935_ = lean_ctor_get(v_a_3908_, 5);
v___x_3936_ = l_Lean_SourceInfo_fromRef(v_ref_3935_, v___x_3932_);
v___x_3937_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18));
v___x_3938_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20));
v___x_3939_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21));
lean_inc_n(v___x_3936_, 8);
v___x_3940_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3936_);
lean_ctor_set(v___x_3940_, 1, v___x_3939_);
v___x_3941_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23));
v___x_3942_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
v___x_3943_ = lean_box(0);
lean_inc_n(v_currMacroScope_3934_, 3);
lean_inc_n(v_quotContext_3933_, 3);
v___x_3944_ = l_Lean_addMacroScope(v_quotContext_3933_, v___x_3943_, v_currMacroScope_3934_);
v___x_3945_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27));
v___x_3946_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3936_);
lean_ctor_set(v___x_3946_, 1, v___x_3942_);
lean_ctor_set(v___x_3946_, 2, v___x_3944_);
lean_ctor_set(v___x_3946_, 3, v___x_3945_);
v___x_3947_ = l_Lean_Syntax_node1(v___x_3936_, v___x_3941_, v___x_3946_);
v___x_3948_ = l_Lean_Syntax_node2(v___x_3936_, v___x_3938_, v___x_3940_, v___x_3947_);
v___x_3949_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28));
v___x_3950_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3936_);
lean_ctor_set(v___x_3950_, 1, v___x_3949_);
v___x_3951_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_3952_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
v___x_3953_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31));
v___x_3954_ = l_Lean_addMacroScope(v_quotContext_3933_, v___x_3953_, v_currMacroScope_3934_);
v___x_3955_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36));
v___x_3956_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3936_);
lean_ctor_set(v___x_3956_, 1, v___x_3952_);
lean_ctor_set(v___x_3956_, 2, v___x_3954_);
lean_ctor_set(v___x_3956_, 3, v___x_3955_);
v___x_3957_ = l_Lean_Syntax_node1(v___x_3936_, v___x_3951_, v___x_3956_);
v___x_3958_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37));
v___x_3959_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3936_);
lean_ctor_set(v___x_3959_, 1, v___x_3958_);
v___x_3960_ = l_Lean_Syntax_node5(v___x_3936_, v___x_3937_, v___x_3948_, v_s_3907_, v___x_3950_, v___x_3957_, v___x_3959_);
v_msg_3911_ = v___x_3960_;
v_quotContext_3912_ = v_quotContext_3933_;
v_currMacroScope_3913_ = v_currMacroScope_3934_;
v_ref_3914_ = v_ref_3935_;
v___y_3915_ = v_a_3909_;
goto v___jp_3910_;
}
else
{
lean_object* v_quotContext_3961_; lean_object* v_currMacroScope_3962_; lean_object* v_ref_3963_; uint8_t v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
v_quotContext_3961_ = lean_ctor_get(v_a_3908_, 1);
v_currMacroScope_3962_ = lean_ctor_get(v_a_3908_, 2);
v_ref_3963_ = lean_ctor_get(v_a_3908_, 5);
v___x_3964_ = 0;
v___x_3965_ = l_Lean_SourceInfo_fromRef(v_ref_3963_, v___x_3964_);
v___x_3966_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39));
v___x_3967_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40));
lean_inc(v___x_3965_);
v___x_3968_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3965_);
lean_ctor_set(v___x_3968_, 1, v___x_3967_);
v___x_3969_ = l_Lean_Syntax_node2(v___x_3965_, v___x_3966_, v___x_3968_, v_s_3907_);
lean_inc(v_currMacroScope_3962_);
lean_inc(v_quotContext_3961_);
v_msg_3911_ = v___x_3969_;
v_quotContext_3912_ = v_quotContext_3961_;
v_currMacroScope_3913_ = v_currMacroScope_3962_;
v_ref_3914_ = v_ref_3963_;
v___y_3915_ = v_a_3909_;
goto v___jp_3910_;
}
v___jp_3910_:
{
uint8_t v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3916_ = 0;
v___x_3917_ = l_Lean_SourceInfo_fromRef(v_ref_3914_, v___x_3916_);
v___x_3918_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3));
v___x_3919_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5));
v___x_3920_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7);
v___x_3921_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9));
v___x_3922_ = l_Lean_addMacroScope(v_quotContext_3912_, v___x_3921_, v_currMacroScope_3913_);
v___x_3923_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12));
lean_inc_n(v___x_3917_, 3);
v___x_3924_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3917_);
lean_ctor_set(v___x_3924_, 1, v___x_3920_);
lean_ctor_set(v___x_3924_, 2, v___x_3922_);
lean_ctor_set(v___x_3924_, 3, v___x_3923_);
v___x_3925_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_3926_ = l_Lean_Syntax_node1(v___x_3917_, v___x_3925_, v_msg_3911_);
v___x_3927_ = l_Lean_Syntax_node2(v___x_3917_, v___x_3919_, v___x_3924_, v___x_3926_);
v___x_3928_ = l_Lean_Syntax_node1(v___x_3917_, v___x_3918_, v___x_3927_);
v___x_3929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3928_);
lean_ctor_set(v___x_3929_, 1, v___y_3915_);
return v___x_3929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___boxed(lean_object* v_s_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_){
_start:
{
lean_object* v_res_3973_; 
v_res_3973_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(v_s_3970_, v_a_3971_, v_a_3972_);
lean_dec_ref(v_a_3971_);
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(lean_object* v_x_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_){
_start:
{
lean_object* v___x_4017_; uint8_t v___x_4018_; 
v___x_4017_ = ((lean_object*)(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1));
lean_inc(v_x_4014_);
v___x_4018_ = l_Lean_Syntax_isOfKind(v_x_4014_, v___x_4017_);
if (v___x_4018_ == 0)
{
lean_object* v___x_4019_; lean_object* v___x_4020_; 
lean_dec(v_x_4014_);
v___x_4019_ = lean_box(1);
v___x_4020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4020_, 0, v___x_4019_);
lean_ctor_set(v___x_4020_, 1, v_a_4016_);
return v___x_4020_;
}
else
{
lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v_a_4024_; lean_object* v_a_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4032_; 
v___x_4021_ = lean_unsigned_to_nat(1u);
v___x_4022_ = l_Lean_Syntax_getArg(v_x_4014_, v___x_4021_);
lean_dec(v_x_4014_);
v___x_4023_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(v___x_4022_, v_a_4015_, v_a_4016_);
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
v_a_4025_ = lean_ctor_get(v___x_4023_, 1);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_4023_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4027_ = v___x_4023_;
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_a_4025_);
lean_inc(v_a_4024_);
lean_dec(v___x_4023_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4030_; 
if (v_isShared_4028_ == 0)
{
v___x_4030_ = v___x_4027_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_a_4024_);
lean_ctor_set(v_reuseFailAlloc_4031_, 1, v_a_4025_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1___boxed(lean_object* v_x_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(v_x_4033_, v_a_4034_, v_a_4035_);
lean_dec_ref(v_a_4034_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue(lean_object* v_msg_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_){
_start:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4065_; 
v___x_4045_ = l_Lean_KVMap_instValueBool;
v___x_4046_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4038_);
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4049_ = v___x_4046_;
v_isShared_4050_ = v_isSharedCheck_4065_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4046_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4065_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
uint8_t v_verbose_4051_; 
v_verbose_4051_ = lean_ctor_get_uint8(v_a_4047_, 0);
lean_dec(v_a_4047_);
if (v_verbose_4051_ == 0)
{
lean_object* v___x_4052_; lean_object* v___x_4054_; 
lean_dec_ref(v_msg_4037_);
v___x_4052_ = lean_box(0);
if (v_isShared_4050_ == 0)
{
lean_ctor_set(v___x_4049_, 0, v___x_4052_);
v___x_4054_ = v___x_4049_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v___x_4052_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
else
{
lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; uint8_t v___x_4059_; 
v___x_4056_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4042_);
v___x_4057_ = l_Lean_Meta_Sym_sym_debug;
v___x_4058_ = l_Lean_Option_get___redArg(v___x_4045_, v___x_4056_, v___x_4057_);
lean_dec_ref(v___x_4056_);
v___x_4059_ = lean_unbox(v___x_4058_);
lean_dec(v___x_4058_);
if (v___x_4059_ == 0)
{
lean_object* v___x_4060_; lean_object* v___x_4062_; 
lean_dec_ref(v_msg_4037_);
v___x_4060_ = lean_box(0);
if (v_isShared_4050_ == 0)
{
lean_ctor_set(v___x_4049_, 0, v___x_4060_);
v___x_4062_ = v___x_4049_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_4060_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
}
}
else
{
lean_object* v___x_4064_; 
lean_del_object(v___x_4049_);
v___x_4064_ = l_Lean_Meta_Sym_reportIssue(v_msg_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
return v___x_4064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue___boxed(lean_object* v_msg_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l_Lean_Meta_Sym_reportDbgIssue(v_msg_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_);
lean_dec(v_a_4072_);
lean_dec_ref(v_a_4071_);
lean_dec(v_a_4070_);
lean_dec_ref(v_a_4069_);
lean_dec(v_a_4068_);
lean_dec_ref(v_a_4067_);
return v_res_4074_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1(void){
_start:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4076_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0));
v___x_4077_ = l_String_toRawSubstring_x27(v___x_4076_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro(lean_object* v_s_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_){
_start:
{
lean_object* v_msg_4097_; lean_object* v_quotContext_4098_; lean_object* v_currMacroScope_4099_; lean_object* v_ref_4100_; lean_object* v___y_4101_; lean_object* v___x_4116_; lean_object* v___x_4117_; uint8_t v___x_4118_; 
lean_inc(v_s_4093_);
v___x_4116_ = l_Lean_Syntax_getKind(v_s_4093_);
v___x_4117_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16));
v___x_4118_ = lean_name_eq(v___x_4116_, v___x_4117_);
lean_dec(v___x_4116_);
if (v___x_4118_ == 0)
{
lean_object* v_quotContext_4119_; lean_object* v_currMacroScope_4120_; lean_object* v_ref_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
v_quotContext_4119_ = lean_ctor_get(v_a_4094_, 1);
v_currMacroScope_4120_ = lean_ctor_get(v_a_4094_, 2);
v_ref_4121_ = lean_ctor_get(v_a_4094_, 5);
v___x_4122_ = l_Lean_SourceInfo_fromRef(v_ref_4121_, v___x_4118_);
v___x_4123_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18));
v___x_4124_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20));
v___x_4125_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21));
lean_inc_n(v___x_4122_, 8);
v___x_4126_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4122_);
lean_ctor_set(v___x_4126_, 1, v___x_4125_);
v___x_4127_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23));
v___x_4128_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
v___x_4129_ = lean_box(0);
lean_inc_n(v_currMacroScope_4120_, 3);
lean_inc_n(v_quotContext_4119_, 3);
v___x_4130_ = l_Lean_addMacroScope(v_quotContext_4119_, v___x_4129_, v_currMacroScope_4120_);
v___x_4131_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27));
v___x_4132_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4122_);
lean_ctor_set(v___x_4132_, 1, v___x_4128_);
lean_ctor_set(v___x_4132_, 2, v___x_4130_);
lean_ctor_set(v___x_4132_, 3, v___x_4131_);
v___x_4133_ = l_Lean_Syntax_node1(v___x_4122_, v___x_4127_, v___x_4132_);
v___x_4134_ = l_Lean_Syntax_node2(v___x_4122_, v___x_4124_, v___x_4126_, v___x_4133_);
v___x_4135_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28));
v___x_4136_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4136_, 0, v___x_4122_);
lean_ctor_set(v___x_4136_, 1, v___x_4135_);
v___x_4137_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4138_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
v___x_4139_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31));
v___x_4140_ = l_Lean_addMacroScope(v_quotContext_4119_, v___x_4139_, v_currMacroScope_4120_);
v___x_4141_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36));
v___x_4142_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4122_);
lean_ctor_set(v___x_4142_, 1, v___x_4138_);
lean_ctor_set(v___x_4142_, 2, v___x_4140_);
lean_ctor_set(v___x_4142_, 3, v___x_4141_);
v___x_4143_ = l_Lean_Syntax_node1(v___x_4122_, v___x_4137_, v___x_4142_);
v___x_4144_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37));
v___x_4145_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4145_, 0, v___x_4122_);
lean_ctor_set(v___x_4145_, 1, v___x_4144_);
v___x_4146_ = l_Lean_Syntax_node5(v___x_4122_, v___x_4123_, v___x_4134_, v_s_4093_, v___x_4136_, v___x_4143_, v___x_4145_);
v_msg_4097_ = v___x_4146_;
v_quotContext_4098_ = v_quotContext_4119_;
v_currMacroScope_4099_ = v_currMacroScope_4120_;
v_ref_4100_ = v_ref_4121_;
v___y_4101_ = v_a_4095_;
goto v___jp_4096_;
}
else
{
lean_object* v_quotContext_4147_; lean_object* v_currMacroScope_4148_; lean_object* v_ref_4149_; uint8_t v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; 
v_quotContext_4147_ = lean_ctor_get(v_a_4094_, 1);
v_currMacroScope_4148_ = lean_ctor_get(v_a_4094_, 2);
v_ref_4149_ = lean_ctor_get(v_a_4094_, 5);
v___x_4150_ = 0;
v___x_4151_ = l_Lean_SourceInfo_fromRef(v_ref_4149_, v___x_4150_);
v___x_4152_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39));
v___x_4153_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40));
lean_inc(v___x_4151_);
v___x_4154_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4151_);
lean_ctor_set(v___x_4154_, 1, v___x_4153_);
v___x_4155_ = l_Lean_Syntax_node2(v___x_4151_, v___x_4152_, v___x_4154_, v_s_4093_);
lean_inc(v_currMacroScope_4148_);
lean_inc(v_quotContext_4147_);
v_msg_4097_ = v___x_4155_;
v_quotContext_4098_ = v_quotContext_4147_;
v_currMacroScope_4099_ = v_currMacroScope_4148_;
v_ref_4100_ = v_ref_4149_;
v___y_4101_ = v_a_4095_;
goto v___jp_4096_;
}
v___jp_4096_:
{
uint8_t v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___x_4102_ = 0;
v___x_4103_ = l_Lean_SourceInfo_fromRef(v_ref_4100_, v___x_4102_);
v___x_4104_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3));
v___x_4105_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5));
v___x_4106_ = lean_obj_once(&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1, &l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1_once, _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1);
v___x_4107_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3));
v___x_4108_ = l_Lean_addMacroScope(v_quotContext_4098_, v___x_4107_, v_currMacroScope_4099_);
v___x_4109_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6));
lean_inc_n(v___x_4103_, 3);
v___x_4110_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4103_);
lean_ctor_set(v___x_4110_, 1, v___x_4106_);
lean_ctor_set(v___x_4110_, 2, v___x_4108_);
lean_ctor_set(v___x_4110_, 3, v___x_4109_);
v___x_4111_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4112_ = l_Lean_Syntax_node1(v___x_4103_, v___x_4111_, v_msg_4097_);
v___x_4113_ = l_Lean_Syntax_node2(v___x_4103_, v___x_4105_, v___x_4110_, v___x_4112_);
v___x_4114_ = l_Lean_Syntax_node1(v___x_4103_, v___x_4104_, v___x_4113_);
v___x_4115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4114_);
lean_ctor_set(v___x_4115_, 1, v___y_4101_);
return v___x_4115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___boxed(lean_object* v_s_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_){
_start:
{
lean_object* v_res_4159_; 
v_res_4159_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v_s_4156_, v_a_4157_, v_a_4158_);
lean_dec_ref(v_a_4157_);
return v_res_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(lean_object* v_x_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_){
_start:
{
lean_object* v___x_4181_; uint8_t v___x_4182_; 
v___x_4181_ = ((lean_object*)(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1));
lean_inc(v_x_4178_);
v___x_4182_ = l_Lean_Syntax_isOfKind(v_x_4178_, v___x_4181_);
if (v___x_4182_ == 0)
{
lean_object* v___x_4183_; lean_object* v___x_4184_; 
lean_dec(v_x_4178_);
v___x_4183_ = lean_box(1);
v___x_4184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4183_);
lean_ctor_set(v___x_4184_, 1, v_a_4180_);
return v___x_4184_;
}
else
{
lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v_a_4188_; lean_object* v_a_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4196_; 
v___x_4185_ = lean_unsigned_to_nat(1u);
v___x_4186_ = l_Lean_Syntax_getArg(v_x_4178_, v___x_4185_);
lean_dec(v_x_4178_);
v___x_4187_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v___x_4186_, v_a_4179_, v_a_4180_);
v_a_4188_ = lean_ctor_get(v___x_4187_, 0);
v_a_4189_ = lean_ctor_get(v___x_4187_, 1);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4187_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4191_ = v___x_4187_;
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_a_4189_);
lean_inc(v_a_4188_);
lean_dec(v___x_4187_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___x_4194_; 
if (v_isShared_4192_ == 0)
{
v___x_4194_ = v___x_4191_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v_a_4188_);
lean_ctor_set(v_reuseFailAlloc_4195_, 1, v_a_4189_);
v___x_4194_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
return v___x_4194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1___boxed(lean_object* v_x_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_){
_start:
{
lean_object* v_res_4200_; 
v_res_4200_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(v_x_4197_, v_a_4198_, v_a_4199_);
lean_dec_ref(v_a_4198_);
return v_res_4200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg(lean_object* v_a_4201_){
_start:
{
lean_object* v___x_4203_; lean_object* v_issues_4204_; lean_object* v___x_4205_; 
v___x_4203_ = lean_st_ref_get(v_a_4201_);
v_issues_4204_ = lean_ctor_get(v___x_4203_, 9);
lean_inc(v_issues_4204_);
lean_dec(v___x_4203_);
v___x_4205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4205_, 0, v_issues_4204_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg___boxed(lean_object* v_a_4206_, lean_object* v_a_4207_){
_start:
{
lean_object* v_res_4208_; 
v_res_4208_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4206_);
lean_dec(v_a_4206_);
return v_res_4208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues(lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_){
_start:
{
lean_object* v___x_4216_; 
v___x_4216_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4210_);
return v___x_4216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___boxed(lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_){
_start:
{
lean_object* v_res_4224_; 
v_res_4224_ = l_Lean_Meta_Sym_getIssues(v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_);
lean_dec(v_a_4222_);
lean_dec_ref(v_a_4221_);
lean_dec(v_a_4220_);
lean_dec_ref(v_a_4219_);
lean_dec(v_a_4218_);
lean_dec_ref(v_a_4217_);
return v_res_4224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(lean_object* v_a_4225_, lean_object* v_issues_4226_, lean_object* v_a_x3f_4227_){
_start:
{
lean_object* v___x_4229_; lean_object* v_share_4230_; lean_object* v_maxFVar_4231_; lean_object* v_proofInstInfo_4232_; lean_object* v_proofInstInfoFVar_4233_; lean_object* v_inferType_4234_; lean_object* v_getLevel_4235_; lean_object* v_congrInfo_4236_; lean_object* v_defEqI_4237_; lean_object* v_extensions_4238_; lean_object* v_issues_4239_; lean_object* v_canon_4240_; lean_object* v_instanceOverrides_4241_; uint8_t v_debug_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4253_; 
v___x_4229_ = lean_st_ref_take(v_a_4225_);
v_share_4230_ = lean_ctor_get(v___x_4229_, 0);
v_maxFVar_4231_ = lean_ctor_get(v___x_4229_, 1);
v_proofInstInfo_4232_ = lean_ctor_get(v___x_4229_, 2);
v_proofInstInfoFVar_4233_ = lean_ctor_get(v___x_4229_, 3);
v_inferType_4234_ = lean_ctor_get(v___x_4229_, 4);
v_getLevel_4235_ = lean_ctor_get(v___x_4229_, 5);
v_congrInfo_4236_ = lean_ctor_get(v___x_4229_, 6);
v_defEqI_4237_ = lean_ctor_get(v___x_4229_, 7);
v_extensions_4238_ = lean_ctor_get(v___x_4229_, 8);
v_issues_4239_ = lean_ctor_get(v___x_4229_, 9);
v_canon_4240_ = lean_ctor_get(v___x_4229_, 10);
v_instanceOverrides_4241_ = lean_ctor_get(v___x_4229_, 11);
v_debug_4242_ = lean_ctor_get_uint8(v___x_4229_, sizeof(void*)*12);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4244_ = v___x_4229_;
v_isShared_4245_ = v_isSharedCheck_4253_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_instanceOverrides_4241_);
lean_inc(v_canon_4240_);
lean_inc(v_issues_4239_);
lean_inc(v_extensions_4238_);
lean_inc(v_defEqI_4237_);
lean_inc(v_congrInfo_4236_);
lean_inc(v_getLevel_4235_);
lean_inc(v_inferType_4234_);
lean_inc(v_proofInstInfoFVar_4233_);
lean_inc(v_proofInstInfo_4232_);
lean_inc(v_maxFVar_4231_);
lean_inc(v_share_4230_);
lean_dec(v___x_4229_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4253_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4249_; 
v___x_4246_ = lean_box(0);
v___x_4247_ = l_List_appendTR___redArg(v_issues_4239_, v_issues_4226_);
if (v_isShared_4245_ == 0)
{
lean_ctor_set(v___x_4244_, 9, v___x_4247_);
v___x_4249_ = v___x_4244_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_share_4230_);
lean_ctor_set(v_reuseFailAlloc_4252_, 1, v_maxFVar_4231_);
lean_ctor_set(v_reuseFailAlloc_4252_, 2, v_proofInstInfo_4232_);
lean_ctor_set(v_reuseFailAlloc_4252_, 3, v_proofInstInfoFVar_4233_);
lean_ctor_set(v_reuseFailAlloc_4252_, 4, v_inferType_4234_);
lean_ctor_set(v_reuseFailAlloc_4252_, 5, v_getLevel_4235_);
lean_ctor_set(v_reuseFailAlloc_4252_, 6, v_congrInfo_4236_);
lean_ctor_set(v_reuseFailAlloc_4252_, 7, v_defEqI_4237_);
lean_ctor_set(v_reuseFailAlloc_4252_, 8, v_extensions_4238_);
lean_ctor_set(v_reuseFailAlloc_4252_, 9, v___x_4247_);
lean_ctor_set(v_reuseFailAlloc_4252_, 10, v_canon_4240_);
lean_ctor_set(v_reuseFailAlloc_4252_, 11, v_instanceOverrides_4241_);
lean_ctor_set_uint8(v_reuseFailAlloc_4252_, sizeof(void*)*12, v_debug_4242_);
v___x_4249_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
lean_object* v___x_4250_; lean_object* v___x_4251_; 
v___x_4250_ = lean_st_ref_put(v_a_4225_, v___x_4249_);
v___x_4251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4246_);
return v___x_4251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0___boxed(lean_object* v_a_4254_, lean_object* v_issues_4255_, lean_object* v_a_x3f_4256_, lean_object* v___y_4257_){
_start:
{
lean_object* v_res_4258_; 
v_res_4258_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4254_, v_issues_4255_, v_a_x3f_4256_);
lean_dec(v_a_x3f_4256_);
lean_dec(v_a_4254_);
return v_res_4258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg(lean_object* v_x_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_){
_start:
{
lean_object* v___x_4267_; lean_object* v_issues_4268_; lean_object* v___x_4269_; lean_object* v_share_4270_; lean_object* v_maxFVar_4271_; lean_object* v_proofInstInfo_4272_; lean_object* v_proofInstInfoFVar_4273_; lean_object* v_inferType_4274_; lean_object* v_getLevel_4275_; lean_object* v_congrInfo_4276_; lean_object* v_defEqI_4277_; lean_object* v_extensions_4278_; lean_object* v_canon_4279_; lean_object* v_instanceOverrides_4280_; uint8_t v_debug_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4319_; 
v___x_4267_ = lean_st_ref_get(v_a_4261_);
v_issues_4268_ = lean_ctor_get(v___x_4267_, 9);
lean_inc(v_issues_4268_);
lean_dec(v___x_4267_);
v___x_4269_ = lean_st_ref_take(v_a_4261_);
v_share_4270_ = lean_ctor_get(v___x_4269_, 0);
v_maxFVar_4271_ = lean_ctor_get(v___x_4269_, 1);
v_proofInstInfo_4272_ = lean_ctor_get(v___x_4269_, 2);
v_proofInstInfoFVar_4273_ = lean_ctor_get(v___x_4269_, 3);
v_inferType_4274_ = lean_ctor_get(v___x_4269_, 4);
v_getLevel_4275_ = lean_ctor_get(v___x_4269_, 5);
v_congrInfo_4276_ = lean_ctor_get(v___x_4269_, 6);
v_defEqI_4277_ = lean_ctor_get(v___x_4269_, 7);
v_extensions_4278_ = lean_ctor_get(v___x_4269_, 8);
v_canon_4279_ = lean_ctor_get(v___x_4269_, 10);
v_instanceOverrides_4280_ = lean_ctor_get(v___x_4269_, 11);
v_debug_4281_ = lean_ctor_get_uint8(v___x_4269_, sizeof(void*)*12);
v_isSharedCheck_4319_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4319_ == 0)
{
lean_object* v_unused_4320_; 
v_unused_4320_ = lean_ctor_get(v___x_4269_, 9);
lean_dec(v_unused_4320_);
v___x_4283_ = v___x_4269_;
v_isShared_4284_ = v_isSharedCheck_4319_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_instanceOverrides_4280_);
lean_inc(v_canon_4279_);
lean_inc(v_extensions_4278_);
lean_inc(v_defEqI_4277_);
lean_inc(v_congrInfo_4276_);
lean_inc(v_getLevel_4275_);
lean_inc(v_inferType_4274_);
lean_inc(v_proofInstInfoFVar_4273_);
lean_inc(v_proofInstInfo_4272_);
lean_inc(v_maxFVar_4271_);
lean_inc(v_share_4270_);
lean_dec(v___x_4269_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4319_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4285_; lean_object* v___x_4287_; 
v___x_4285_ = lean_box(0);
if (v_isShared_4284_ == 0)
{
lean_ctor_set(v___x_4283_, 9, v___x_4285_);
v___x_4287_ = v___x_4283_;
goto v_reusejp_4286_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_share_4270_);
lean_ctor_set(v_reuseFailAlloc_4318_, 1, v_maxFVar_4271_);
lean_ctor_set(v_reuseFailAlloc_4318_, 2, v_proofInstInfo_4272_);
lean_ctor_set(v_reuseFailAlloc_4318_, 3, v_proofInstInfoFVar_4273_);
lean_ctor_set(v_reuseFailAlloc_4318_, 4, v_inferType_4274_);
lean_ctor_set(v_reuseFailAlloc_4318_, 5, v_getLevel_4275_);
lean_ctor_set(v_reuseFailAlloc_4318_, 6, v_congrInfo_4276_);
lean_ctor_set(v_reuseFailAlloc_4318_, 7, v_defEqI_4277_);
lean_ctor_set(v_reuseFailAlloc_4318_, 8, v_extensions_4278_);
lean_ctor_set(v_reuseFailAlloc_4318_, 9, v___x_4285_);
lean_ctor_set(v_reuseFailAlloc_4318_, 10, v_canon_4279_);
lean_ctor_set(v_reuseFailAlloc_4318_, 11, v_instanceOverrides_4280_);
lean_ctor_set_uint8(v_reuseFailAlloc_4318_, sizeof(void*)*12, v_debug_4281_);
v___x_4287_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4286_;
}
v_reusejp_4286_:
{
lean_object* v___x_4288_; lean_object* v_r_4289_; 
v___x_4288_ = lean_st_ref_put(v_a_4261_, v___x_4287_);
lean_inc(v_a_4265_);
lean_inc_ref(v_a_4264_);
lean_inc(v_a_4263_);
lean_inc_ref(v_a_4262_);
lean_inc(v_a_4261_);
lean_inc_ref(v_a_4260_);
v_r_4289_ = lean_apply_7(v_x_4259_, v_a_4260_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_, v_a_4265_, lean_box(0));
if (lean_obj_tag(v_r_4289_) == 0)
{
lean_object* v_a_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4306_; 
v_a_4290_ = lean_ctor_get(v_r_4289_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v_r_4289_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4292_ = v_r_4289_;
v_isShared_4293_ = v_isSharedCheck_4306_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_a_4290_);
lean_dec(v_r_4289_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4306_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
lean_object* v___x_4295_; 
lean_inc(v_a_4290_);
if (v_isShared_4293_ == 0)
{
lean_ctor_set_tag(v___x_4292_, 1);
v___x_4295_ = v___x_4292_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v_a_4290_);
v___x_4295_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
lean_object* v___x_4296_; lean_object* v___x_4298_; uint8_t v_isShared_4299_; uint8_t v_isSharedCheck_4303_; 
v___x_4296_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4261_, v_issues_4268_, v___x_4295_);
lean_dec_ref(v___x_4295_);
v_isSharedCheck_4303_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4303_ == 0)
{
lean_object* v_unused_4304_; 
v_unused_4304_ = lean_ctor_get(v___x_4296_, 0);
lean_dec(v_unused_4304_);
v___x_4298_ = v___x_4296_;
v_isShared_4299_ = v_isSharedCheck_4303_;
goto v_resetjp_4297_;
}
else
{
lean_dec(v___x_4296_);
v___x_4298_ = lean_box(0);
v_isShared_4299_ = v_isSharedCheck_4303_;
goto v_resetjp_4297_;
}
v_resetjp_4297_:
{
lean_object* v___x_4301_; 
if (v_isShared_4299_ == 0)
{
lean_ctor_set(v___x_4298_, 0, v_a_4290_);
v___x_4301_ = v___x_4298_;
goto v_reusejp_4300_;
}
else
{
lean_object* v_reuseFailAlloc_4302_; 
v_reuseFailAlloc_4302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4302_, 0, v_a_4290_);
v___x_4301_ = v_reuseFailAlloc_4302_;
goto v_reusejp_4300_;
}
v_reusejp_4300_:
{
return v___x_4301_;
}
}
}
}
}
else
{
lean_object* v_a_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4316_; 
v_a_4307_ = lean_ctor_get(v_r_4289_, 0);
lean_inc(v_a_4307_);
lean_dec_ref_known(v_r_4289_, 1);
v___x_4308_ = lean_box(0);
v___x_4309_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4261_, v_issues_4268_, v___x_4308_);
v_isSharedCheck_4316_ = !lean_is_exclusive(v___x_4309_);
if (v_isSharedCheck_4316_ == 0)
{
lean_object* v_unused_4317_; 
v_unused_4317_ = lean_ctor_get(v___x_4309_, 0);
lean_dec(v_unused_4317_);
v___x_4311_ = v___x_4309_;
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
else
{
lean_dec(v___x_4309_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4314_; 
if (v_isShared_4312_ == 0)
{
lean_ctor_set_tag(v___x_4311_, 1);
lean_ctor_set(v___x_4311_, 0, v_a_4307_);
v___x_4314_ = v___x_4311_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_a_4307_);
v___x_4314_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
return v___x_4314_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___boxed(lean_object* v_x_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_4321_, v_a_4322_, v_a_4323_, v_a_4324_, v_a_4325_, v_a_4326_, v_a_4327_);
lean_dec(v_a_4327_);
lean_dec_ref(v_a_4326_);
lean_dec(v_a_4325_);
lean_dec_ref(v_a_4324_);
lean_dec(v_a_4323_);
lean_dec_ref(v_a_4322_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext(lean_object* v_00_u03b1_4330_, lean_object* v_x_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_){
_start:
{
lean_object* v___x_4339_; 
v___x_4339_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_4331_, v_a_4332_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_, v_a_4337_);
return v___x_4339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___boxed(lean_object* v_00_u03b1_4340_, lean_object* v_x_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_){
_start:
{
lean_object* v_res_4349_; 
v_res_4349_ = l_Lean_Meta_Sym_withNewIssueContext(v_00_u03b1_4340_, v_x_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
lean_dec(v_a_4347_);
lean_dec_ref(v_a_4346_);
lean_dec(v_a_4345_);
lean_dec_ref(v_a_4344_);
lean_dec(v_a_4343_);
lean_dec_ref(v_a_4342_);
return v_res_4349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4350_, lean_object* v_vals_4351_, lean_object* v_i_4352_, lean_object* v_k_4353_){
_start:
{
lean_object* v___x_4358_; uint8_t v___x_4359_; 
v___x_4358_ = lean_array_get_size(v_keys_4350_);
v___x_4359_ = lean_nat_dec_lt(v_i_4352_, v___x_4358_);
if (v___x_4359_ == 0)
{
lean_object* v___x_4360_; 
lean_dec(v_i_4352_);
v___x_4360_ = lean_box(0);
return v___x_4360_;
}
else
{
lean_object* v_fst_4361_; lean_object* v_snd_4362_; lean_object* v_k_x27_4363_; lean_object* v_fst_4364_; lean_object* v_snd_4365_; size_t v___x_4366_; size_t v___x_4367_; uint8_t v___x_4368_; 
v_fst_4361_ = lean_ctor_get(v_k_4353_, 0);
v_snd_4362_ = lean_ctor_get(v_k_4353_, 1);
v_k_x27_4363_ = lean_array_fget_borrowed(v_keys_4350_, v_i_4352_);
v_fst_4364_ = lean_ctor_get(v_k_x27_4363_, 0);
v_snd_4365_ = lean_ctor_get(v_k_x27_4363_, 1);
v___x_4366_ = lean_ptr_addr(v_fst_4361_);
v___x_4367_ = lean_ptr_addr(v_fst_4364_);
v___x_4368_ = lean_usize_dec_eq(v___x_4366_, v___x_4367_);
if (v___x_4368_ == 0)
{
goto v___jp_4354_;
}
else
{
size_t v___x_4369_; size_t v___x_4370_; uint8_t v___x_4371_; 
v___x_4369_ = lean_ptr_addr(v_snd_4362_);
v___x_4370_ = lean_ptr_addr(v_snd_4365_);
v___x_4371_ = lean_usize_dec_eq(v___x_4369_, v___x_4370_);
if (v___x_4371_ == 0)
{
goto v___jp_4354_;
}
else
{
lean_object* v___x_4372_; lean_object* v___x_4373_; 
v___x_4372_ = lean_array_fget_borrowed(v_vals_4351_, v_i_4352_);
lean_dec(v_i_4352_);
lean_inc(v___x_4372_);
v___x_4373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4373_, 0, v___x_4372_);
return v___x_4373_;
}
}
}
v___jp_4354_:
{
lean_object* v___x_4355_; lean_object* v___x_4356_; 
v___x_4355_ = lean_unsigned_to_nat(1u);
v___x_4356_ = lean_nat_add(v_i_4352_, v___x_4355_);
lean_dec(v_i_4352_);
v_i_4352_ = v___x_4356_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4374_, lean_object* v_vals_4375_, lean_object* v_i_4376_, lean_object* v_k_4377_){
_start:
{
lean_object* v_res_4378_; 
v_res_4378_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_4374_, v_vals_4375_, v_i_4376_, v_k_4377_);
lean_dec_ref(v_k_4377_);
lean_dec_ref(v_vals_4375_);
lean_dec_ref(v_keys_4374_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(lean_object* v_x_4379_, size_t v_x_4380_, lean_object* v_x_4381_){
_start:
{
if (lean_obj_tag(v_x_4379_) == 0)
{
lean_object* v_es_4382_; lean_object* v___x_4383_; size_t v___x_4384_; size_t v___x_4385_; lean_object* v_j_4386_; lean_object* v___x_4387_; 
v_es_4382_ = lean_ctor_get(v_x_4379_, 0);
v___x_4383_ = lean_box(2);
v___x_4384_ = ((size_t)31ULL);
v___x_4385_ = lean_usize_land(v_x_4380_, v___x_4384_);
v_j_4386_ = lean_usize_to_nat(v___x_4385_);
v___x_4387_ = lean_array_get_borrowed(v___x_4383_, v_es_4382_, v_j_4386_);
lean_dec(v_j_4386_);
switch(lean_obj_tag(v___x_4387_))
{
case 0:
{
lean_object* v_key_4388_; lean_object* v_val_4389_; lean_object* v_fst_4390_; lean_object* v_snd_4391_; lean_object* v_fst_4392_; lean_object* v_snd_4393_; size_t v___x_4394_; size_t v___x_4395_; uint8_t v___x_4396_; 
v_key_4388_ = lean_ctor_get(v___x_4387_, 0);
v_val_4389_ = lean_ctor_get(v___x_4387_, 1);
v_fst_4390_ = lean_ctor_get(v_x_4381_, 0);
v_snd_4391_ = lean_ctor_get(v_x_4381_, 1);
v_fst_4392_ = lean_ctor_get(v_key_4388_, 0);
v_snd_4393_ = lean_ctor_get(v_key_4388_, 1);
v___x_4394_ = lean_ptr_addr(v_fst_4390_);
v___x_4395_ = lean_ptr_addr(v_fst_4392_);
v___x_4396_ = lean_usize_dec_eq(v___x_4394_, v___x_4395_);
if (v___x_4396_ == 0)
{
lean_object* v___x_4397_; 
v___x_4397_ = lean_box(0);
return v___x_4397_;
}
else
{
size_t v___x_4398_; size_t v___x_4399_; uint8_t v___x_4400_; 
v___x_4398_ = lean_ptr_addr(v_snd_4391_);
v___x_4399_ = lean_ptr_addr(v_snd_4393_);
v___x_4400_ = lean_usize_dec_eq(v___x_4398_, v___x_4399_);
if (v___x_4400_ == 0)
{
lean_object* v___x_4401_; 
v___x_4401_ = lean_box(0);
return v___x_4401_;
}
else
{
lean_object* v___x_4402_; 
lean_inc(v_val_4389_);
v___x_4402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4402_, 0, v_val_4389_);
return v___x_4402_;
}
}
}
case 1:
{
lean_object* v_node_4403_; size_t v___x_4404_; size_t v___x_4405_; 
v_node_4403_ = lean_ctor_get(v___x_4387_, 0);
v___x_4404_ = ((size_t)5ULL);
v___x_4405_ = lean_usize_shift_right(v_x_4380_, v___x_4404_);
v_x_4379_ = v_node_4403_;
v_x_4380_ = v___x_4405_;
goto _start;
}
default: 
{
lean_object* v___x_4407_; 
v___x_4407_ = lean_box(0);
return v___x_4407_;
}
}
}
else
{
lean_object* v_ks_4408_; lean_object* v_vs_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
v_ks_4408_ = lean_ctor_get(v_x_4379_, 0);
v_vs_4409_ = lean_ctor_get(v_x_4379_, 1);
v___x_4410_ = lean_unsigned_to_nat(0u);
v___x_4411_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_ks_4408_, v_vs_4409_, v___x_4410_, v_x_4381_);
return v___x_4411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg___boxed(lean_object* v_x_4412_, lean_object* v_x_4413_, lean_object* v_x_4414_){
_start:
{
size_t v_x_2884__boxed_4415_; lean_object* v_res_4416_; 
v_x_2884__boxed_4415_ = lean_unbox_usize(v_x_4413_);
lean_dec(v_x_4413_);
v_res_4416_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4412_, v_x_2884__boxed_4415_, v_x_4414_);
lean_dec_ref(v_x_4414_);
lean_dec_ref(v_x_4412_);
return v_res_4416_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(lean_object* v_x_4417_, lean_object* v_x_4418_){
_start:
{
lean_object* v_fst_4419_; lean_object* v_snd_4420_; size_t v___x_4421_; size_t v___x_4422_; size_t v___x_4423_; uint64_t v___x_4424_; size_t v___x_4425_; size_t v___x_4426_; uint64_t v___x_4427_; uint64_t v___x_4428_; size_t v___x_4429_; lean_object* v___x_4430_; 
v_fst_4419_ = lean_ctor_get(v_x_4418_, 0);
v_snd_4420_ = lean_ctor_get(v_x_4418_, 1);
v___x_4421_ = lean_ptr_addr(v_fst_4419_);
v___x_4422_ = ((size_t)3ULL);
v___x_4423_ = lean_usize_shift_right(v___x_4421_, v___x_4422_);
v___x_4424_ = lean_usize_to_uint64(v___x_4423_);
v___x_4425_ = lean_ptr_addr(v_snd_4420_);
v___x_4426_ = lean_usize_shift_right(v___x_4425_, v___x_4422_);
v___x_4427_ = lean_usize_to_uint64(v___x_4426_);
v___x_4428_ = lean_uint64_mix_hash(v___x_4424_, v___x_4427_);
v___x_4429_ = lean_uint64_to_usize(v___x_4428_);
v___x_4430_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4417_, v___x_4429_, v_x_4418_);
return v___x_4430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg___boxed(lean_object* v_x_4431_, lean_object* v_x_4432_){
_start:
{
lean_object* v_res_4433_; 
v_res_4433_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_4431_, v_x_4432_);
lean_dec_ref(v_x_4432_);
lean_dec_ref(v_x_4431_);
return v_res_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_4434_, lean_object* v_x_4435_, lean_object* v_x_4436_, lean_object* v_x_4437_){
_start:
{
lean_object* v_ks_4438_; lean_object* v_vs_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4475_; 
v_ks_4438_ = lean_ctor_get(v_x_4434_, 0);
v_vs_4439_ = lean_ctor_get(v_x_4434_, 1);
v_isSharedCheck_4475_ = !lean_is_exclusive(v_x_4434_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4441_ = v_x_4434_;
v_isShared_4442_ = v_isSharedCheck_4475_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_vs_4439_);
lean_inc(v_ks_4438_);
lean_dec(v_x_4434_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4475_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v___x_4450_; uint8_t v___x_4451_; 
v___x_4450_ = lean_array_get_size(v_ks_4438_);
v___x_4451_ = lean_nat_dec_lt(v_x_4435_, v___x_4450_);
if (v___x_4451_ == 0)
{
lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
lean_del_object(v___x_4441_);
lean_dec(v_x_4435_);
v___x_4452_ = lean_array_push(v_ks_4438_, v_x_4436_);
v___x_4453_ = lean_array_push(v_vs_4439_, v_x_4437_);
v___x_4454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4454_, 0, v___x_4452_);
lean_ctor_set(v___x_4454_, 1, v___x_4453_);
return v___x_4454_;
}
else
{
lean_object* v_fst_4455_; lean_object* v_snd_4456_; lean_object* v_k_x27_4457_; lean_object* v_fst_4458_; lean_object* v_snd_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4474_; 
v_fst_4455_ = lean_ctor_get(v_x_4436_, 0);
v_snd_4456_ = lean_ctor_get(v_x_4436_, 1);
v_k_x27_4457_ = lean_array_fget(v_ks_4438_, v_x_4435_);
v_fst_4458_ = lean_ctor_get(v_k_x27_4457_, 0);
v_snd_4459_ = lean_ctor_get(v_k_x27_4457_, 1);
v_isSharedCheck_4474_ = !lean_is_exclusive(v_k_x27_4457_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4461_ = v_k_x27_4457_;
v_isShared_4462_ = v_isSharedCheck_4474_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_snd_4459_);
lean_inc(v_fst_4458_);
lean_dec(v_k_x27_4457_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4474_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
size_t v___x_4463_; size_t v___x_4464_; uint8_t v___x_4465_; 
v___x_4463_ = lean_ptr_addr(v_fst_4455_);
v___x_4464_ = lean_ptr_addr(v_fst_4458_);
lean_dec(v_fst_4458_);
v___x_4465_ = lean_usize_dec_eq(v___x_4463_, v___x_4464_);
if (v___x_4465_ == 0)
{
lean_del_object(v___x_4461_);
lean_dec(v_snd_4459_);
goto v___jp_4443_;
}
else
{
size_t v___x_4466_; size_t v___x_4467_; uint8_t v___x_4468_; 
v___x_4466_ = lean_ptr_addr(v_snd_4456_);
v___x_4467_ = lean_ptr_addr(v_snd_4459_);
lean_dec(v_snd_4459_);
v___x_4468_ = lean_usize_dec_eq(v___x_4466_, v___x_4467_);
if (v___x_4468_ == 0)
{
lean_del_object(v___x_4461_);
goto v___jp_4443_;
}
else
{
lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4472_; 
lean_del_object(v___x_4441_);
v___x_4469_ = lean_array_fset(v_ks_4438_, v_x_4435_, v_x_4436_);
v___x_4470_ = lean_array_fset(v_vs_4439_, v_x_4435_, v_x_4437_);
lean_dec(v_x_4435_);
if (v_isShared_4462_ == 0)
{
lean_ctor_set_tag(v___x_4461_, 1);
lean_ctor_set(v___x_4461_, 1, v___x_4470_);
lean_ctor_set(v___x_4461_, 0, v___x_4469_);
v___x_4472_ = v___x_4461_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v___x_4469_);
lean_ctor_set(v_reuseFailAlloc_4473_, 1, v___x_4470_);
v___x_4472_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
return v___x_4472_;
}
}
}
}
}
v___jp_4443_:
{
lean_object* v___x_4445_; 
if (v_isShared_4442_ == 0)
{
v___x_4445_ = v___x_4441_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_ks_4438_);
lean_ctor_set(v_reuseFailAlloc_4449_, 1, v_vs_4439_);
v___x_4445_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; 
v___x_4446_ = lean_unsigned_to_nat(1u);
v___x_4447_ = lean_nat_add(v_x_4435_, v___x_4446_);
lean_dec(v_x_4435_);
v_x_4434_ = v___x_4445_;
v_x_4435_ = v___x_4447_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(lean_object* v_n_4476_, lean_object* v_k_4477_, lean_object* v_v_4478_){
_start:
{
lean_object* v___x_4479_; lean_object* v___x_4480_; 
v___x_4479_ = lean_unsigned_to_nat(0u);
v___x_4480_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_n_4476_, v___x_4479_, v_k_4477_, v_v_4478_);
return v___x_4480_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4481_; 
v___x_4481_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_4481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(lean_object* v_x_4482_, size_t v_x_4483_, size_t v_x_4484_, lean_object* v_x_4485_, lean_object* v_x_4486_){
_start:
{
if (lean_obj_tag(v_x_4482_) == 0)
{
lean_object* v_es_4487_; size_t v___x_4488_; size_t v___x_4489_; lean_object* v_j_4490_; lean_object* v___x_4491_; uint8_t v___x_4492_; 
v_es_4487_ = lean_ctor_get(v_x_4482_, 0);
v___x_4488_ = ((size_t)31ULL);
v___x_4489_ = lean_usize_land(v_x_4483_, v___x_4488_);
v_j_4490_ = lean_usize_to_nat(v___x_4489_);
v___x_4491_ = lean_array_get_size(v_es_4487_);
v___x_4492_ = lean_nat_dec_lt(v_j_4490_, v___x_4491_);
if (v___x_4492_ == 0)
{
lean_dec(v_j_4490_);
lean_dec(v_x_4486_);
lean_dec_ref(v_x_4485_);
return v_x_4482_;
}
else
{
lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4541_; 
lean_inc_ref(v_es_4487_);
v_isSharedCheck_4541_ = !lean_is_exclusive(v_x_4482_);
if (v_isSharedCheck_4541_ == 0)
{
lean_object* v_unused_4542_; 
v_unused_4542_ = lean_ctor_get(v_x_4482_, 0);
lean_dec(v_unused_4542_);
v___x_4494_ = v_x_4482_;
v_isShared_4495_ = v_isSharedCheck_4541_;
goto v_resetjp_4493_;
}
else
{
lean_dec(v_x_4482_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4541_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v_v_4496_; lean_object* v___x_4497_; lean_object* v_xs_x27_4498_; lean_object* v___y_4500_; 
v_v_4496_ = lean_array_fget(v_es_4487_, v_j_4490_);
v___x_4497_ = lean_box(0);
v_xs_x27_4498_ = lean_array_fset(v_es_4487_, v_j_4490_, v___x_4497_);
switch(lean_obj_tag(v_v_4496_))
{
case 0:
{
lean_object* v_key_4505_; lean_object* v_val_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4526_; 
v_key_4505_ = lean_ctor_get(v_v_4496_, 0);
v_val_4506_ = lean_ctor_get(v_v_4496_, 1);
v_isSharedCheck_4526_ = !lean_is_exclusive(v_v_4496_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4508_ = v_v_4496_;
v_isShared_4509_ = v_isSharedCheck_4526_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_val_4506_);
lean_inc(v_key_4505_);
lean_dec(v_v_4496_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4526_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v_fst_4513_; lean_object* v_snd_4514_; lean_object* v_fst_4515_; lean_object* v_snd_4516_; size_t v___x_4517_; size_t v___x_4518_; uint8_t v___x_4519_; 
v_fst_4513_ = lean_ctor_get(v_x_4485_, 0);
v_snd_4514_ = lean_ctor_get(v_x_4485_, 1);
v_fst_4515_ = lean_ctor_get(v_key_4505_, 0);
v_snd_4516_ = lean_ctor_get(v_key_4505_, 1);
v___x_4517_ = lean_ptr_addr(v_fst_4513_);
v___x_4518_ = lean_ptr_addr(v_fst_4515_);
v___x_4519_ = lean_usize_dec_eq(v___x_4517_, v___x_4518_);
if (v___x_4519_ == 0)
{
lean_del_object(v___x_4508_);
goto v___jp_4510_;
}
else
{
size_t v___x_4520_; size_t v___x_4521_; uint8_t v___x_4522_; 
v___x_4520_ = lean_ptr_addr(v_snd_4514_);
v___x_4521_ = lean_ptr_addr(v_snd_4516_);
v___x_4522_ = lean_usize_dec_eq(v___x_4520_, v___x_4521_);
if (v___x_4522_ == 0)
{
lean_del_object(v___x_4508_);
goto v___jp_4510_;
}
else
{
lean_object* v___x_4524_; 
lean_dec(v_val_4506_);
lean_dec(v_key_4505_);
if (v_isShared_4509_ == 0)
{
lean_ctor_set(v___x_4508_, 1, v_x_4486_);
lean_ctor_set(v___x_4508_, 0, v_x_4485_);
v___x_4524_ = v___x_4508_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_x_4485_);
lean_ctor_set(v_reuseFailAlloc_4525_, 1, v_x_4486_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
v___y_4500_ = v___x_4524_;
goto v___jp_4499_;
}
}
}
v___jp_4510_:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; 
v___x_4511_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4505_, v_val_4506_, v_x_4485_, v_x_4486_);
v___x_4512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4512_, 0, v___x_4511_);
v___y_4500_ = v___x_4512_;
goto v___jp_4499_;
}
}
}
case 1:
{
lean_object* v_node_4527_; lean_object* v___x_4529_; uint8_t v_isShared_4530_; uint8_t v_isSharedCheck_4539_; 
v_node_4527_ = lean_ctor_get(v_v_4496_, 0);
v_isSharedCheck_4539_ = !lean_is_exclusive(v_v_4496_);
if (v_isSharedCheck_4539_ == 0)
{
v___x_4529_ = v_v_4496_;
v_isShared_4530_ = v_isSharedCheck_4539_;
goto v_resetjp_4528_;
}
else
{
lean_inc(v_node_4527_);
lean_dec(v_v_4496_);
v___x_4529_ = lean_box(0);
v_isShared_4530_ = v_isSharedCheck_4539_;
goto v_resetjp_4528_;
}
v_resetjp_4528_:
{
size_t v___x_4531_; size_t v___x_4532_; size_t v___x_4533_; size_t v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4537_; 
v___x_4531_ = ((size_t)5ULL);
v___x_4532_ = lean_usize_shift_right(v_x_4483_, v___x_4531_);
v___x_4533_ = ((size_t)1ULL);
v___x_4534_ = lean_usize_add(v_x_4484_, v___x_4533_);
v___x_4535_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_node_4527_, v___x_4532_, v___x_4534_, v_x_4485_, v_x_4486_);
if (v_isShared_4530_ == 0)
{
lean_ctor_set(v___x_4529_, 0, v___x_4535_);
v___x_4537_ = v___x_4529_;
goto v_reusejp_4536_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v___x_4535_);
v___x_4537_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4536_;
}
v_reusejp_4536_:
{
v___y_4500_ = v___x_4537_;
goto v___jp_4499_;
}
}
}
default: 
{
lean_object* v___x_4540_; 
v___x_4540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4540_, 0, v_x_4485_);
lean_ctor_set(v___x_4540_, 1, v_x_4486_);
v___y_4500_ = v___x_4540_;
goto v___jp_4499_;
}
}
v___jp_4499_:
{
lean_object* v___x_4501_; lean_object* v___x_4503_; 
v___x_4501_ = lean_array_fset(v_xs_x27_4498_, v_j_4490_, v___y_4500_);
lean_dec(v_j_4490_);
if (v_isShared_4495_ == 0)
{
lean_ctor_set(v___x_4494_, 0, v___x_4501_);
v___x_4503_ = v___x_4494_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v___x_4501_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
return v___x_4503_;
}
}
}
}
}
else
{
lean_object* v_ks_4543_; lean_object* v_vs_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4562_; 
v_ks_4543_ = lean_ctor_get(v_x_4482_, 0);
v_vs_4544_ = lean_ctor_get(v_x_4482_, 1);
v_isSharedCheck_4562_ = !lean_is_exclusive(v_x_4482_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4546_ = v_x_4482_;
v_isShared_4547_ = v_isSharedCheck_4562_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_vs_4544_);
lean_inc(v_ks_4543_);
lean_dec(v_x_4482_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4562_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4549_; 
if (v_isShared_4547_ == 0)
{
v___x_4549_ = v___x_4546_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_ks_4543_);
lean_ctor_set(v_reuseFailAlloc_4561_, 1, v_vs_4544_);
v___x_4549_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
lean_object* v_newNode_4550_; size_t v___x_4551_; uint8_t v___x_4552_; 
v_newNode_4550_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v___x_4549_, v_x_4485_, v_x_4486_);
v___x_4551_ = ((size_t)7ULL);
v___x_4552_ = lean_usize_dec_le(v___x_4551_, v_x_4484_);
if (v___x_4552_ == 0)
{
lean_object* v___x_4553_; lean_object* v___x_4554_; uint8_t v___x_4555_; 
v___x_4553_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4550_);
v___x_4554_ = lean_unsigned_to_nat(4u);
v___x_4555_ = lean_nat_dec_lt(v___x_4553_, v___x_4554_);
lean_dec(v___x_4553_);
if (v___x_4555_ == 0)
{
lean_object* v_ks_4556_; lean_object* v_vs_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
v_ks_4556_ = lean_ctor_get(v_newNode_4550_, 0);
lean_inc_ref(v_ks_4556_);
v_vs_4557_ = lean_ctor_get(v_newNode_4550_, 1);
lean_inc_ref(v_vs_4557_);
lean_dec_ref(v_newNode_4550_);
v___x_4558_ = lean_unsigned_to_nat(0u);
v___x_4559_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0);
v___x_4560_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_x_4484_, v_ks_4556_, v_vs_4557_, v___x_4558_, v___x_4559_);
lean_dec_ref(v_vs_4557_);
lean_dec_ref(v_ks_4556_);
return v___x_4560_;
}
else
{
return v_newNode_4550_;
}
}
else
{
return v_newNode_4550_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(size_t v_depth_4563_, lean_object* v_keys_4564_, lean_object* v_vals_4565_, lean_object* v_i_4566_, lean_object* v_entries_4567_){
_start:
{
lean_object* v___x_4568_; uint8_t v___x_4569_; 
v___x_4568_ = lean_array_get_size(v_keys_4564_);
v___x_4569_ = lean_nat_dec_lt(v_i_4566_, v___x_4568_);
if (v___x_4569_ == 0)
{
lean_dec(v_i_4566_);
return v_entries_4567_;
}
else
{
lean_object* v_k_4570_; lean_object* v_fst_4571_; lean_object* v_snd_4572_; lean_object* v_v_4573_; size_t v___x_4574_; size_t v___x_4575_; size_t v___x_4576_; uint64_t v___x_4577_; size_t v___x_4578_; size_t v___x_4579_; uint64_t v___x_4580_; uint64_t v___x_4581_; size_t v_h_4582_; size_t v___x_4583_; lean_object* v___x_4584_; size_t v___x_4585_; size_t v___x_4586_; size_t v___x_4587_; size_t v_h_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; 
v_k_4570_ = lean_array_fget_borrowed(v_keys_4564_, v_i_4566_);
v_fst_4571_ = lean_ctor_get(v_k_4570_, 0);
v_snd_4572_ = lean_ctor_get(v_k_4570_, 1);
v_v_4573_ = lean_array_fget_borrowed(v_vals_4565_, v_i_4566_);
v___x_4574_ = lean_ptr_addr(v_fst_4571_);
v___x_4575_ = ((size_t)3ULL);
v___x_4576_ = lean_usize_shift_right(v___x_4574_, v___x_4575_);
v___x_4577_ = lean_usize_to_uint64(v___x_4576_);
v___x_4578_ = lean_ptr_addr(v_snd_4572_);
v___x_4579_ = lean_usize_shift_right(v___x_4578_, v___x_4575_);
v___x_4580_ = lean_usize_to_uint64(v___x_4579_);
v___x_4581_ = lean_uint64_mix_hash(v___x_4577_, v___x_4580_);
v_h_4582_ = lean_uint64_to_usize(v___x_4581_);
v___x_4583_ = ((size_t)5ULL);
v___x_4584_ = lean_unsigned_to_nat(1u);
v___x_4585_ = ((size_t)1ULL);
v___x_4586_ = lean_usize_sub(v_depth_4563_, v___x_4585_);
v___x_4587_ = lean_usize_mul(v___x_4583_, v___x_4586_);
v_h_4588_ = lean_usize_shift_right(v_h_4582_, v___x_4587_);
v___x_4589_ = lean_nat_add(v_i_4566_, v___x_4584_);
lean_dec(v_i_4566_);
lean_inc(v_v_4573_);
lean_inc(v_k_4570_);
v___x_4590_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_entries_4567_, v_h_4588_, v_depth_4563_, v_k_4570_, v_v_4573_);
v_i_4566_ = v___x_4589_;
v_entries_4567_ = v___x_4590_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_4592_, lean_object* v_keys_4593_, lean_object* v_vals_4594_, lean_object* v_i_4595_, lean_object* v_entries_4596_){
_start:
{
size_t v_depth_boxed_4597_; lean_object* v_res_4598_; 
v_depth_boxed_4597_ = lean_unbox_usize(v_depth_4592_);
lean_dec(v_depth_4592_);
v_res_4598_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_boxed_4597_, v_keys_4593_, v_vals_4594_, v_i_4595_, v_entries_4596_);
lean_dec_ref(v_vals_4594_);
lean_dec_ref(v_keys_4593_);
return v_res_4598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___boxed(lean_object* v_x_4599_, lean_object* v_x_4600_, lean_object* v_x_4601_, lean_object* v_x_4602_, lean_object* v_x_4603_){
_start:
{
size_t v_x_3090__boxed_4604_; size_t v_x_3091__boxed_4605_; lean_object* v_res_4606_; 
v_x_3090__boxed_4604_ = lean_unbox_usize(v_x_4600_);
lean_dec(v_x_4600_);
v_x_3091__boxed_4605_ = lean_unbox_usize(v_x_4601_);
lean_dec(v_x_4601_);
v_res_4606_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4599_, v_x_3090__boxed_4604_, v_x_3091__boxed_4605_, v_x_4602_, v_x_4603_);
return v_res_4606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(lean_object* v_x_4607_, lean_object* v_x_4608_, lean_object* v_x_4609_){
_start:
{
lean_object* v_fst_4610_; lean_object* v_snd_4611_; size_t v___x_4612_; size_t v___x_4613_; size_t v___x_4614_; uint64_t v___x_4615_; size_t v___x_4616_; size_t v___x_4617_; uint64_t v___x_4618_; uint64_t v___x_4619_; size_t v___x_4620_; size_t v___x_4621_; lean_object* v___x_4622_; 
v_fst_4610_ = lean_ctor_get(v_x_4608_, 0);
v_snd_4611_ = lean_ctor_get(v_x_4608_, 1);
v___x_4612_ = lean_ptr_addr(v_fst_4610_);
v___x_4613_ = ((size_t)3ULL);
v___x_4614_ = lean_usize_shift_right(v___x_4612_, v___x_4613_);
v___x_4615_ = lean_usize_to_uint64(v___x_4614_);
v___x_4616_ = lean_ptr_addr(v_snd_4611_);
v___x_4617_ = lean_usize_shift_right(v___x_4616_, v___x_4613_);
v___x_4618_ = lean_usize_to_uint64(v___x_4617_);
v___x_4619_ = lean_uint64_mix_hash(v___x_4615_, v___x_4618_);
v___x_4620_ = lean_uint64_to_usize(v___x_4619_);
v___x_4621_ = ((size_t)1ULL);
v___x_4622_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4607_, v___x_4620_, v___x_4621_, v_x_4608_, v_x_4609_);
return v___x_4622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object* v_s_4623_, lean_object* v_t_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_){
_start:
{
lean_object* v_key_4631_; lean_object* v___x_4632_; lean_object* v_defEqI_4633_; lean_object* v___x_4634_; 
lean_inc_ref(v_t_4624_);
lean_inc_ref(v_s_4623_);
v_key_4631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_4631_, 0, v_s_4623_);
lean_ctor_set(v_key_4631_, 1, v_t_4624_);
v___x_4632_ = lean_st_ref_get(v_a_4625_);
v_defEqI_4633_ = lean_ctor_get(v___x_4632_, 7);
lean_inc_ref(v_defEqI_4633_);
lean_dec(v___x_4632_);
v___x_4634_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_defEqI_4633_, v_key_4631_);
lean_dec_ref(v_defEqI_4633_);
if (lean_obj_tag(v___x_4634_) == 1)
{
lean_object* v_val_4635_; lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4642_; 
lean_dec_ref_known(v_key_4631_, 2);
lean_dec_ref(v_t_4624_);
lean_dec_ref(v_s_4623_);
v_val_4635_ = lean_ctor_get(v___x_4634_, 0);
v_isSharedCheck_4642_ = !lean_is_exclusive(v___x_4634_);
if (v_isSharedCheck_4642_ == 0)
{
v___x_4637_ = v___x_4634_;
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
else
{
lean_inc(v_val_4635_);
lean_dec(v___x_4634_);
v___x_4637_ = lean_box(0);
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
v_resetjp_4636_:
{
lean_object* v___x_4640_; 
if (v_isShared_4638_ == 0)
{
lean_ctor_set_tag(v___x_4637_, 0);
v___x_4640_ = v___x_4637_;
goto v_reusejp_4639_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v_val_4635_);
v___x_4640_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4639_;
}
v_reusejp_4639_:
{
return v___x_4640_;
}
}
}
else
{
lean_object* v___x_4643_; 
lean_dec(v___x_4634_);
v___x_4643_ = l_Lean_Meta_isDefEqI(v_s_4623_, v_t_4624_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_);
if (lean_obj_tag(v___x_4643_) == 0)
{
lean_object* v_a_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4674_; 
v_a_4644_ = lean_ctor_get(v___x_4643_, 0);
v_isSharedCheck_4674_ = !lean_is_exclusive(v___x_4643_);
if (v_isSharedCheck_4674_ == 0)
{
v___x_4646_ = v___x_4643_;
v_isShared_4647_ = v_isSharedCheck_4674_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_a_4644_);
lean_dec(v___x_4643_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4674_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v___x_4648_; lean_object* v_share_4649_; lean_object* v_maxFVar_4650_; lean_object* v_proofInstInfo_4651_; lean_object* v_proofInstInfoFVar_4652_; lean_object* v_inferType_4653_; lean_object* v_getLevel_4654_; lean_object* v_congrInfo_4655_; lean_object* v_defEqI_4656_; lean_object* v_extensions_4657_; lean_object* v_issues_4658_; lean_object* v_canon_4659_; lean_object* v_instanceOverrides_4660_; uint8_t v_debug_4661_; lean_object* v___x_4663_; uint8_t v_isShared_4664_; uint8_t v_isSharedCheck_4673_; 
v___x_4648_ = lean_st_ref_take(v_a_4625_);
v_share_4649_ = lean_ctor_get(v___x_4648_, 0);
v_maxFVar_4650_ = lean_ctor_get(v___x_4648_, 1);
v_proofInstInfo_4651_ = lean_ctor_get(v___x_4648_, 2);
v_proofInstInfoFVar_4652_ = lean_ctor_get(v___x_4648_, 3);
v_inferType_4653_ = lean_ctor_get(v___x_4648_, 4);
v_getLevel_4654_ = lean_ctor_get(v___x_4648_, 5);
v_congrInfo_4655_ = lean_ctor_get(v___x_4648_, 6);
v_defEqI_4656_ = lean_ctor_get(v___x_4648_, 7);
v_extensions_4657_ = lean_ctor_get(v___x_4648_, 8);
v_issues_4658_ = lean_ctor_get(v___x_4648_, 9);
v_canon_4659_ = lean_ctor_get(v___x_4648_, 10);
v_instanceOverrides_4660_ = lean_ctor_get(v___x_4648_, 11);
v_debug_4661_ = lean_ctor_get_uint8(v___x_4648_, sizeof(void*)*12);
v_isSharedCheck_4673_ = !lean_is_exclusive(v___x_4648_);
if (v_isSharedCheck_4673_ == 0)
{
v___x_4663_ = v___x_4648_;
v_isShared_4664_ = v_isSharedCheck_4673_;
goto v_resetjp_4662_;
}
else
{
lean_inc(v_instanceOverrides_4660_);
lean_inc(v_canon_4659_);
lean_inc(v_issues_4658_);
lean_inc(v_extensions_4657_);
lean_inc(v_defEqI_4656_);
lean_inc(v_congrInfo_4655_);
lean_inc(v_getLevel_4654_);
lean_inc(v_inferType_4653_);
lean_inc(v_proofInstInfoFVar_4652_);
lean_inc(v_proofInstInfo_4651_);
lean_inc(v_maxFVar_4650_);
lean_inc(v_share_4649_);
lean_dec(v___x_4648_);
v___x_4663_ = lean_box(0);
v_isShared_4664_ = v_isSharedCheck_4673_;
goto v_resetjp_4662_;
}
v_resetjp_4662_:
{
lean_object* v___x_4665_; lean_object* v___x_4667_; 
lean_inc(v_a_4644_);
v___x_4665_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_defEqI_4656_, v_key_4631_, v_a_4644_);
if (v_isShared_4664_ == 0)
{
lean_ctor_set(v___x_4663_, 7, v___x_4665_);
v___x_4667_ = v___x_4663_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_share_4649_);
lean_ctor_set(v_reuseFailAlloc_4672_, 1, v_maxFVar_4650_);
lean_ctor_set(v_reuseFailAlloc_4672_, 2, v_proofInstInfo_4651_);
lean_ctor_set(v_reuseFailAlloc_4672_, 3, v_proofInstInfoFVar_4652_);
lean_ctor_set(v_reuseFailAlloc_4672_, 4, v_inferType_4653_);
lean_ctor_set(v_reuseFailAlloc_4672_, 5, v_getLevel_4654_);
lean_ctor_set(v_reuseFailAlloc_4672_, 6, v_congrInfo_4655_);
lean_ctor_set(v_reuseFailAlloc_4672_, 7, v___x_4665_);
lean_ctor_set(v_reuseFailAlloc_4672_, 8, v_extensions_4657_);
lean_ctor_set(v_reuseFailAlloc_4672_, 9, v_issues_4658_);
lean_ctor_set(v_reuseFailAlloc_4672_, 10, v_canon_4659_);
lean_ctor_set(v_reuseFailAlloc_4672_, 11, v_instanceOverrides_4660_);
lean_ctor_set_uint8(v_reuseFailAlloc_4672_, sizeof(void*)*12, v_debug_4661_);
v___x_4667_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
lean_object* v___x_4668_; lean_object* v___x_4670_; 
v___x_4668_ = lean_st_ref_put(v_a_4625_, v___x_4667_);
if (v_isShared_4647_ == 0)
{
v___x_4670_ = v___x_4646_;
goto v_reusejp_4669_;
}
else
{
lean_object* v_reuseFailAlloc_4671_; 
v_reuseFailAlloc_4671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4671_, 0, v_a_4644_);
v___x_4670_ = v_reuseFailAlloc_4671_;
goto v_reusejp_4669_;
}
v_reusejp_4669_:
{
return v___x_4670_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_4631_, 2);
return v___x_4643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg___boxed(lean_object* v_s_4675_, lean_object* v_t_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_){
_start:
{
lean_object* v_res_4683_; 
v_res_4683_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_4675_, v_t_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_);
lean_dec(v_a_4681_);
lean_dec_ref(v_a_4680_);
lean_dec(v_a_4679_);
lean_dec_ref(v_a_4678_);
lean_dec(v_a_4677_);
return v_res_4683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI(lean_object* v_s_4684_, lean_object* v_t_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_){
_start:
{
lean_object* v___x_4693_; 
v___x_4693_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_4684_, v_t_4685_, v_a_4687_, v_a_4688_, v_a_4689_, v_a_4690_, v_a_4691_);
return v___x_4693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___boxed(lean_object* v_s_4694_, lean_object* v_t_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_){
_start:
{
lean_object* v_res_4703_; 
v_res_4703_ = l_Lean_Meta_Sym_isDefEqI(v_s_4694_, v_t_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_);
lean_dec(v_a_4701_);
lean_dec_ref(v_a_4700_);
lean_dec(v_a_4699_);
lean_dec_ref(v_a_4698_);
lean_dec(v_a_4697_);
lean_dec_ref(v_a_4696_);
return v_res_4703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(lean_object* v_00_u03b2_4704_, lean_object* v_x_4705_, lean_object* v_x_4706_){
_start:
{
lean_object* v___x_4707_; 
v___x_4707_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_4705_, v_x_4706_);
return v___x_4707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___boxed(lean_object* v_00_u03b2_4708_, lean_object* v_x_4709_, lean_object* v_x_4710_){
_start:
{
lean_object* v_res_4711_; 
v_res_4711_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(v_00_u03b2_4708_, v_x_4709_, v_x_4710_);
lean_dec_ref(v_x_4710_);
lean_dec_ref(v_x_4709_);
return v_res_4711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1(lean_object* v_00_u03b2_4712_, lean_object* v_x_4713_, lean_object* v_x_4714_, lean_object* v_x_4715_){
_start:
{
lean_object* v___x_4716_; 
v___x_4716_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_x_4713_, v_x_4714_, v_x_4715_);
return v___x_4716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(lean_object* v_00_u03b2_4717_, lean_object* v_x_4718_, size_t v_x_4719_, lean_object* v_x_4720_){
_start:
{
lean_object* v___x_4721_; 
v___x_4721_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4718_, v_x_4719_, v_x_4720_);
return v___x_4721_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4722_, lean_object* v_x_4723_, lean_object* v_x_4724_, lean_object* v_x_4725_){
_start:
{
size_t v_x_3386__boxed_4726_; lean_object* v_res_4727_; 
v_x_3386__boxed_4726_ = lean_unbox_usize(v_x_4724_);
lean_dec(v_x_4724_);
v_res_4727_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(v_00_u03b2_4722_, v_x_4723_, v_x_3386__boxed_4726_, v_x_4725_);
lean_dec_ref(v_x_4725_);
lean_dec_ref(v_x_4723_);
return v_res_4727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(lean_object* v_00_u03b2_4728_, lean_object* v_x_4729_, size_t v_x_4730_, size_t v_x_4731_, lean_object* v_x_4732_, lean_object* v_x_4733_){
_start:
{
lean_object* v___x_4734_; 
v___x_4734_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4729_, v_x_4730_, v_x_4731_, v_x_4732_, v_x_4733_);
return v___x_4734_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4735_, lean_object* v_x_4736_, lean_object* v_x_4737_, lean_object* v_x_4738_, lean_object* v_x_4739_, lean_object* v_x_4740_){
_start:
{
size_t v_x_3397__boxed_4741_; size_t v_x_3398__boxed_4742_; lean_object* v_res_4743_; 
v_x_3397__boxed_4741_ = lean_unbox_usize(v_x_4737_);
lean_dec(v_x_4737_);
v_x_3398__boxed_4742_ = lean_unbox_usize(v_x_4738_);
lean_dec(v_x_4738_);
v_res_4743_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(v_00_u03b2_4735_, v_x_4736_, v_x_3397__boxed_4741_, v_x_3398__boxed_4742_, v_x_4739_, v_x_4740_);
return v_res_4743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4744_, lean_object* v_keys_4745_, lean_object* v_vals_4746_, lean_object* v_heq_4747_, lean_object* v_i_4748_, lean_object* v_k_4749_){
_start:
{
lean_object* v___x_4750_; 
v___x_4750_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_4745_, v_vals_4746_, v_i_4748_, v_k_4749_);
return v___x_4750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4751_, lean_object* v_keys_4752_, lean_object* v_vals_4753_, lean_object* v_heq_4754_, lean_object* v_i_4755_, lean_object* v_k_4756_){
_start:
{
lean_object* v_res_4757_; 
v_res_4757_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(v_00_u03b2_4751_, v_keys_4752_, v_vals_4753_, v_heq_4754_, v_i_4755_, v_k_4756_);
lean_dec_ref(v_k_4756_);
lean_dec_ref(v_vals_4753_);
lean_dec_ref(v_keys_4752_);
return v_res_4757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4758_, lean_object* v_n_4759_, lean_object* v_k_4760_, lean_object* v_v_4761_){
_start:
{
lean_object* v___x_4762_; 
v___x_4762_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v_n_4759_, v_k_4760_, v_v_4761_);
return v___x_4762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_4763_, size_t v_depth_4764_, lean_object* v_keys_4765_, lean_object* v_vals_4766_, lean_object* v_heq_4767_, lean_object* v_i_4768_, lean_object* v_entries_4769_){
_start:
{
lean_object* v___x_4770_; 
v___x_4770_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_4764_, v_keys_4765_, v_vals_4766_, v_i_4768_, v_entries_4769_);
return v___x_4770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_4771_, lean_object* v_depth_4772_, lean_object* v_keys_4773_, lean_object* v_vals_4774_, lean_object* v_heq_4775_, lean_object* v_i_4776_, lean_object* v_entries_4777_){
_start:
{
size_t v_depth_boxed_4778_; lean_object* v_res_4779_; 
v_depth_boxed_4778_ = lean_unbox_usize(v_depth_4772_);
lean_dec(v_depth_4772_);
v_res_4779_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(v_00_u03b2_4771_, v_depth_boxed_4778_, v_keys_4773_, v_vals_4774_, v_heq_4775_, v_i_4776_, v_entries_4777_);
lean_dec_ref(v_vals_4774_);
lean_dec_ref(v_keys_4773_);
return v_res_4779_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_4780_, lean_object* v_x_4781_, lean_object* v_x_4782_, lean_object* v_x_4783_, lean_object* v_x_4784_){
_start:
{
lean_object* v___x_4785_; 
v___x_4785_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_x_4781_, v_x_4782_, v_x_4783_, v_x_4784_);
return v___x_4785_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__0(void){
_start:
{
lean_object* v___x_4786_; lean_object* v___f_4787_; 
v___x_4786_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_4787_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4787_, 0, v___x_4786_);
return v___f_4787_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__1(void){
_start:
{
lean_object* v___x_4788_; lean_object* v___f_4789_; 
v___x_4788_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_4789_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4789_, 0, v___x_4788_);
return v___f_4789_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2(void){
_start:
{
lean_object* v___f_4790_; lean_object* v___f_4791_; lean_object* v___x_4792_; 
v___f_4790_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__1, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__1_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__1);
v___f_4791_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__0, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__0);
v___x_4792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4792_, 0, v___f_4791_);
lean_ctor_set(v___x_4792_, 1, v___f_4790_);
return v___x_4792_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__3(void){
_start:
{
lean_object* v___x_4793_; lean_object* v___f_4794_; 
v___x_4793_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2);
v___f_4794_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4794_, 0, v___x_4793_);
return v___f_4794_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__4(void){
_start:
{
lean_object* v___x_4795_; lean_object* v___f_4796_; 
v___x_4795_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2);
v___f_4796_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4796_, 0, v___x_4795_);
return v___f_4796_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5(void){
_start:
{
lean_object* v___f_4797_; lean_object* v___f_4798_; lean_object* v___x_4799_; 
v___f_4797_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__4, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__4_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__4);
v___f_4798_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__3, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__3_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__3);
v___x_4799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4799_, 0, v___f_4798_);
lean_ctor_set(v___x_4799_, 1, v___f_4797_);
return v___x_4799_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__6(void){
_start:
{
lean_object* v___x_4800_; lean_object* v___f_4801_; 
v___x_4800_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5);
v___f_4801_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4801_, 0, v___x_4800_);
return v___f_4801_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__7(void){
_start:
{
lean_object* v___x_4802_; lean_object* v___f_4803_; 
v___x_4802_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5);
v___f_4803_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4803_, 0, v___x_4802_);
return v___f_4803_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8(void){
_start:
{
lean_object* v___f_4804_; lean_object* v___f_4805_; lean_object* v___x_4806_; 
v___f_4804_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__7, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__7_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__7);
v___f_4805_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__6, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__6_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__6);
v___x_4806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4806_, 0, v___f_4805_);
lean_ctor_set(v___x_4806_, 1, v___f_4804_);
return v___x_4806_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__9(void){
_start:
{
lean_object* v___x_4807_; lean_object* v___f_4808_; 
v___x_4807_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8);
v___f_4808_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4808_, 0, v___x_4807_);
return v___f_4808_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__10(void){
_start:
{
lean_object* v___x_4809_; lean_object* v___f_4810_; 
v___x_4809_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8);
v___f_4810_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4810_, 0, v___x_4809_);
return v___f_4810_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__11(void){
_start:
{
lean_object* v___f_4811_; lean_object* v___f_4812_; lean_object* v___x_4813_; 
v___f_4811_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__10, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__10_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__10);
v___f_4812_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__9, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__9_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__9);
v___x_4813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4813_, 0, v___f_4812_);
lean_ctor_set(v___x_4813_, 1, v___f_4811_);
return v___x_4813_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__16(void){
_start:
{
lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; 
v___x_4818_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_4819_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__15));
v___x_4820_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__14));
v___x_4821_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_4820_, v___x_4819_, v___x_4818_);
return v___x_4821_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__17(void){
_start:
{
lean_object* v___x_4822_; lean_object* v___f_4823_; lean_object* v___f_4824_; lean_object* v___x_4825_; 
v___x_4822_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__16, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__16_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__16);
v___f_4823_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__13));
v___f_4824_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__12));
v___x_4825_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_4824_, v___f_4823_, v___x_4822_);
return v___x_4825_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__18(void){
_start:
{
lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; 
v___x_4826_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__17, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__17_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__17);
v___x_4827_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__15));
v___x_4828_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__14));
v___x_4829_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_4828_, v___x_4827_, v___x_4826_);
return v___x_4829_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__19(void){
_start:
{
lean_object* v___x_4830_; lean_object* v___f_4831_; lean_object* v___f_4832_; lean_object* v___x_4833_; 
v___x_4830_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__18, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__18_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__18);
v___f_4831_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__13));
v___f_4832_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__12));
v___x_4833_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_4832_, v___f_4831_, v___x_4830_);
return v___x_4833_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__20(void){
_start:
{
lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___f_4836_; 
v___x_4834_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__15));
v___x_4835_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_4836_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4836_, 0, v___x_4835_);
lean_closure_set(v___f_4836_, 1, v___x_4834_);
return v___f_4836_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__21(void){
_start:
{
lean_object* v___f_4837_; lean_object* v___f_4838_; lean_object* v___f_4839_; 
v___f_4837_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__13));
v___f_4838_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__20, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__20_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__20);
v___f_4839_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4839_, 0, v___f_4838_);
lean_closure_set(v___f_4839_, 1, v___f_4837_);
return v___f_4839_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__23(void){
_start:
{
lean_object* v___x_4841_; lean_object* v___x_4842_; 
v___x_4841_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__22));
v___x_4842_ = l_Lean_stringToMessageData(v___x_4841_);
return v___x_4842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg(){
_start:
{
lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v_toApplicative_4846_; lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4913_; 
v___x_4844_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0);
v___x_4845_ = l_StateRefT_x27_instMonad___redArg(v___x_4844_);
v_toApplicative_4846_ = lean_ctor_get(v___x_4845_, 0);
v_isSharedCheck_4913_ = !lean_is_exclusive(v___x_4845_);
if (v_isSharedCheck_4913_ == 0)
{
lean_object* v_unused_4914_; 
v_unused_4914_ = lean_ctor_get(v___x_4845_, 1);
lean_dec(v_unused_4914_);
v___x_4848_ = v___x_4845_;
v_isShared_4849_ = v_isSharedCheck_4913_;
goto v_resetjp_4847_;
}
else
{
lean_inc(v_toApplicative_4846_);
lean_dec(v___x_4845_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4913_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
lean_object* v_toFunctor_4850_; lean_object* v_toSeq_4851_; lean_object* v_toSeqLeft_4852_; lean_object* v_toSeqRight_4853_; lean_object* v___x_4855_; uint8_t v_isShared_4856_; uint8_t v_isSharedCheck_4911_; 
v_toFunctor_4850_ = lean_ctor_get(v_toApplicative_4846_, 0);
v_toSeq_4851_ = lean_ctor_get(v_toApplicative_4846_, 2);
v_toSeqLeft_4852_ = lean_ctor_get(v_toApplicative_4846_, 3);
v_toSeqRight_4853_ = lean_ctor_get(v_toApplicative_4846_, 4);
v_isSharedCheck_4911_ = !lean_is_exclusive(v_toApplicative_4846_);
if (v_isSharedCheck_4911_ == 0)
{
lean_object* v_unused_4912_; 
v_unused_4912_ = lean_ctor_get(v_toApplicative_4846_, 1);
lean_dec(v_unused_4912_);
v___x_4855_ = v_toApplicative_4846_;
v_isShared_4856_ = v_isSharedCheck_4911_;
goto v_resetjp_4854_;
}
else
{
lean_inc(v_toSeqRight_4853_);
lean_inc(v_toSeqLeft_4852_);
lean_inc(v_toSeq_4851_);
lean_inc(v_toFunctor_4850_);
lean_dec(v_toApplicative_4846_);
v___x_4855_ = lean_box(0);
v_isShared_4856_ = v_isSharedCheck_4911_;
goto v_resetjp_4854_;
}
v_resetjp_4854_:
{
lean_object* v___f_4857_; lean_object* v___f_4858_; lean_object* v___f_4859_; lean_object* v___f_4860_; lean_object* v___x_4861_; lean_object* v___f_4862_; lean_object* v___f_4863_; lean_object* v___f_4864_; lean_object* v___x_4866_; 
v___f_4857_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1));
v___f_4858_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4850_);
v___f_4859_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4859_, 0, v_toFunctor_4850_);
v___f_4860_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4860_, 0, v_toFunctor_4850_);
v___x_4861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4861_, 0, v___f_4859_);
lean_ctor_set(v___x_4861_, 1, v___f_4860_);
v___f_4862_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4862_, 0, v_toSeqRight_4853_);
v___f_4863_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4863_, 0, v_toSeqLeft_4852_);
v___f_4864_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4864_, 0, v_toSeq_4851_);
if (v_isShared_4856_ == 0)
{
lean_ctor_set(v___x_4855_, 4, v___f_4862_);
lean_ctor_set(v___x_4855_, 3, v___f_4863_);
lean_ctor_set(v___x_4855_, 2, v___f_4864_);
lean_ctor_set(v___x_4855_, 1, v___f_4857_);
lean_ctor_set(v___x_4855_, 0, v___x_4861_);
v___x_4866_ = v___x_4855_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4910_; 
v_reuseFailAlloc_4910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4910_, 0, v___x_4861_);
lean_ctor_set(v_reuseFailAlloc_4910_, 1, v___f_4857_);
lean_ctor_set(v_reuseFailAlloc_4910_, 2, v___f_4864_);
lean_ctor_set(v_reuseFailAlloc_4910_, 3, v___f_4863_);
lean_ctor_set(v_reuseFailAlloc_4910_, 4, v___f_4862_);
v___x_4866_ = v_reuseFailAlloc_4910_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
lean_object* v___x_4868_; 
if (v_isShared_4849_ == 0)
{
lean_ctor_set(v___x_4848_, 1, v___f_4858_);
lean_ctor_set(v___x_4848_, 0, v___x_4866_);
v___x_4868_ = v___x_4848_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v___x_4866_);
lean_ctor_set(v_reuseFailAlloc_4909_, 1, v___f_4858_);
v___x_4868_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
lean_object* v___x_4869_; lean_object* v_toApplicative_4870_; lean_object* v___x_4872_; uint8_t v_isShared_4873_; uint8_t v_isSharedCheck_4907_; 
v___x_4869_ = l_StateRefT_x27_instMonad___redArg(v___x_4868_);
v_toApplicative_4870_ = lean_ctor_get(v___x_4869_, 0);
v_isSharedCheck_4907_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4907_ == 0)
{
lean_object* v_unused_4908_; 
v_unused_4908_ = lean_ctor_get(v___x_4869_, 1);
lean_dec(v_unused_4908_);
v___x_4872_ = v___x_4869_;
v_isShared_4873_ = v_isSharedCheck_4907_;
goto v_resetjp_4871_;
}
else
{
lean_inc(v_toApplicative_4870_);
lean_dec(v___x_4869_);
v___x_4872_ = lean_box(0);
v_isShared_4873_ = v_isSharedCheck_4907_;
goto v_resetjp_4871_;
}
v_resetjp_4871_:
{
lean_object* v_toFunctor_4874_; lean_object* v_toSeq_4875_; lean_object* v_toSeqLeft_4876_; lean_object* v_toSeqRight_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4905_; 
v_toFunctor_4874_ = lean_ctor_get(v_toApplicative_4870_, 0);
v_toSeq_4875_ = lean_ctor_get(v_toApplicative_4870_, 2);
v_toSeqLeft_4876_ = lean_ctor_get(v_toApplicative_4870_, 3);
v_toSeqRight_4877_ = lean_ctor_get(v_toApplicative_4870_, 4);
v_isSharedCheck_4905_ = !lean_is_exclusive(v_toApplicative_4870_);
if (v_isSharedCheck_4905_ == 0)
{
lean_object* v_unused_4906_; 
v_unused_4906_ = lean_ctor_get(v_toApplicative_4870_, 1);
lean_dec(v_unused_4906_);
v___x_4879_ = v_toApplicative_4870_;
v_isShared_4880_ = v_isSharedCheck_4905_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_toSeqRight_4877_);
lean_inc(v_toSeqLeft_4876_);
lean_inc(v_toSeq_4875_);
lean_inc(v_toFunctor_4874_);
lean_dec(v_toApplicative_4870_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4905_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
lean_object* v___f_4881_; lean_object* v___f_4882_; lean_object* v___f_4883_; lean_object* v___f_4884_; lean_object* v___x_4885_; lean_object* v___f_4886_; lean_object* v___f_4887_; lean_object* v___f_4888_; lean_object* v___x_4890_; 
v___f_4881_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3));
v___f_4882_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4874_);
v___f_4883_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4883_, 0, v_toFunctor_4874_);
v___f_4884_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4884_, 0, v_toFunctor_4874_);
v___x_4885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4885_, 0, v___f_4883_);
lean_ctor_set(v___x_4885_, 1, v___f_4884_);
v___f_4886_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4886_, 0, v_toSeqRight_4877_);
v___f_4887_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4887_, 0, v_toSeqLeft_4876_);
v___f_4888_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4888_, 0, v_toSeq_4875_);
if (v_isShared_4880_ == 0)
{
lean_ctor_set(v___x_4879_, 4, v___f_4886_);
lean_ctor_set(v___x_4879_, 3, v___f_4887_);
lean_ctor_set(v___x_4879_, 2, v___f_4888_);
lean_ctor_set(v___x_4879_, 1, v___f_4881_);
lean_ctor_set(v___x_4879_, 0, v___x_4885_);
v___x_4890_ = v___x_4879_;
goto v_reusejp_4889_;
}
else
{
lean_object* v_reuseFailAlloc_4904_; 
v_reuseFailAlloc_4904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4904_, 0, v___x_4885_);
lean_ctor_set(v_reuseFailAlloc_4904_, 1, v___f_4881_);
lean_ctor_set(v_reuseFailAlloc_4904_, 2, v___f_4888_);
lean_ctor_set(v_reuseFailAlloc_4904_, 3, v___f_4887_);
lean_ctor_set(v_reuseFailAlloc_4904_, 4, v___f_4886_);
v___x_4890_ = v_reuseFailAlloc_4904_;
goto v_reusejp_4889_;
}
v_reusejp_4889_:
{
lean_object* v___x_4892_; 
if (v_isShared_4873_ == 0)
{
lean_ctor_set(v___x_4872_, 1, v___f_4882_);
lean_ctor_set(v___x_4872_, 0, v___x_4890_);
v___x_4892_ = v___x_4872_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v___x_4890_);
lean_ctor_set(v_reuseFailAlloc_4903_, 1, v___f_4882_);
v___x_4892_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v_toMonadRef_4897_; lean_object* v___f_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; 
v___x_4893_ = l_StateRefT_x27_instMonad___redArg(v___x_4892_);
v___x_4894_ = l_ReaderT_instMonad___redArg(v___x_4893_);
v___x_4895_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__11, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__11_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__11);
v___x_4896_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__19, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__19_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__19);
v_toMonadRef_4897_ = lean_ctor_get(v___x_4896_, 0);
v___f_4898_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__21, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__21_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__21);
lean_inc_ref(v___x_4894_);
v___x_4899_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_4898_, v___x_4894_);
lean_inc_ref(v_toMonadRef_4897_);
v___x_4900_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4900_, 0, v___x_4895_);
lean_ctor_set(v___x_4900_, 1, v_toMonadRef_4897_);
lean_ctor_set(v___x_4900_, 2, v___x_4899_);
v___x_4901_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__23, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__23_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__23);
v___x_4902_ = l_Lean_throwError___redArg(v___x_4894_, v___x_4900_, v___x_4901_);
return v___x_4902_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___boxed(lean_object* v___dummy_4915_){
_start:
{
lean_object* v_res_4916_; 
v_res_4916_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v_res_4916_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0(void){
_start:
{
lean_object* v___x_4917_; 
v___x_4917_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_4917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object* v_00_u03b1_4918_){
_start:
{
lean_object* v___x_4919_; 
v___x_4919_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__0, &l_Lean_Meta_Sym_instInhabitedSymM___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0);
return v___x_4919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(lean_object* v_ext_4920_, lean_object* v_extensions_4921_){
_start:
{
lean_object* v_id_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; 
v_id_4923_ = lean_ctor_get(v_ext_4920_, 0);
v___x_4924_ = l_Lean_Meta_Sym_instInhabitedSymExtensionState;
v___x_4925_ = lean_array_get_borrowed(v___x_4924_, v_extensions_4921_, v_id_4923_);
lean_inc(v___x_4925_);
v___x_4926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4926_, 0, v___x_4925_);
return v___x_4926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg___boxed(lean_object* v_ext_4927_, lean_object* v_extensions_4928_, lean_object* v_a_4929_){
_start:
{
lean_object* v_res_4930_; 
v_res_4930_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_4927_, v_extensions_4928_);
lean_dec_ref(v_extensions_4928_);
lean_dec_ref(v_ext_4927_);
return v_res_4930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(lean_object* v_00_u03c3_4931_, lean_object* v_ext_4932_, lean_object* v_extensions_4933_){
_start:
{
lean_object* v___x_4935_; 
v___x_4935_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_4932_, v_extensions_4933_);
return v___x_4935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___boxed(lean_object* v_00_u03c3_4936_, lean_object* v_ext_4937_, lean_object* v_extensions_4938_, lean_object* v_a_4939_){
_start:
{
lean_object* v_res_4940_; 
v_res_4940_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(v_00_u03c3_4936_, v_ext_4937_, v_extensions_4938_);
lean_dec_ref(v_extensions_4938_);
lean_dec_ref(v_ext_4937_);
return v_res_4940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg(lean_object* v_ext_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_){
_start:
{
lean_object* v___x_4945_; lean_object* v_extensions_4946_; lean_object* v_ref_4947_; lean_object* v___x_4948_; 
v___x_4945_ = lean_st_ref_get(v_a_4942_);
v_extensions_4946_ = lean_ctor_get(v___x_4945_, 8);
lean_inc_ref(v_extensions_4946_);
lean_dec(v___x_4945_);
v_ref_4947_ = lean_ctor_get(v_a_4943_, 2);
v___x_4948_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_4941_, v_extensions_4946_);
lean_dec_ref(v_extensions_4946_);
if (lean_obj_tag(v___x_4948_) == 0)
{
lean_object* v_a_4949_; lean_object* v___x_4951_; uint8_t v_isShared_4952_; uint8_t v_isSharedCheck_4956_; 
v_a_4949_ = lean_ctor_get(v___x_4948_, 0);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4948_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4951_ = v___x_4948_;
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
else
{
lean_inc(v_a_4949_);
lean_dec(v___x_4948_);
v___x_4951_ = lean_box(0);
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
v_resetjp_4950_:
{
lean_object* v___x_4954_; 
if (v_isShared_4952_ == 0)
{
v___x_4954_ = v___x_4951_;
goto v_reusejp_4953_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v_a_4949_);
v___x_4954_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4953_;
}
v_reusejp_4953_:
{
return v___x_4954_;
}
}
}
else
{
lean_object* v_a_4957_; lean_object* v___x_4959_; uint8_t v_isShared_4960_; uint8_t v_isSharedCheck_4968_; 
v_a_4957_ = lean_ctor_get(v___x_4948_, 0);
v_isSharedCheck_4968_ = !lean_is_exclusive(v___x_4948_);
if (v_isSharedCheck_4968_ == 0)
{
v___x_4959_ = v___x_4948_;
v_isShared_4960_ = v_isSharedCheck_4968_;
goto v_resetjp_4958_;
}
else
{
lean_inc(v_a_4957_);
lean_dec(v___x_4948_);
v___x_4959_ = lean_box(0);
v_isShared_4960_ = v_isSharedCheck_4968_;
goto v_resetjp_4958_;
}
v_resetjp_4958_:
{
lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4966_; 
v___x_4961_ = lean_io_error_to_string(v_a_4957_);
v___x_4962_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4962_, 0, v___x_4961_);
v___x_4963_ = l_Lean_MessageData_ofFormat(v___x_4962_);
lean_inc(v_ref_4947_);
v___x_4964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4964_, 0, v_ref_4947_);
lean_ctor_set(v___x_4964_, 1, v___x_4963_);
if (v_isShared_4960_ == 0)
{
lean_ctor_set(v___x_4959_, 0, v___x_4964_);
v___x_4966_ = v___x_4959_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v___x_4964_);
v___x_4966_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
return v___x_4966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg___boxed(lean_object* v_ext_4969_, lean_object* v_a_4970_, lean_object* v_a_4971_, lean_object* v_a_4972_){
_start:
{
lean_object* v_res_4973_; 
v_res_4973_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_4969_, v_a_4970_, v_a_4971_);
lean_dec_ref(v_a_4971_);
lean_dec(v_a_4970_);
lean_dec_ref(v_ext_4969_);
return v_res_4973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState(lean_object* v_00_u03c3_4974_, lean_object* v_ext_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_){
_start:
{
lean_object* v___x_4983_; 
v___x_4983_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_4975_, v_a_4977_, v_a_4980_);
return v___x_4983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___boxed(lean_object* v_00_u03c3_4984_, lean_object* v_ext_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_){
_start:
{
lean_object* v_res_4993_; 
v_res_4993_ = l_Lean_Meta_Sym_SymExtension_getState(v_00_u03c3_4984_, v_ext_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_);
lean_dec(v_a_4991_);
lean_dec_ref(v_a_4990_);
lean_dec(v_a_4989_);
lean_dec_ref(v_a_4988_);
lean_dec(v_a_4987_);
lean_dec_ref(v_a_4986_);
lean_dec_ref(v_ext_4985_);
return v_res_4993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(lean_object* v_ext_4994_, lean_object* v_f_4995_, lean_object* v_a_4996_){
_start:
{
lean_object* v___x_4998_; lean_object* v_share_4999_; lean_object* v_maxFVar_5000_; lean_object* v_proofInstInfo_5001_; lean_object* v_proofInstInfoFVar_5002_; lean_object* v_inferType_5003_; lean_object* v_getLevel_5004_; lean_object* v_congrInfo_5005_; lean_object* v_defEqI_5006_; lean_object* v_extensions_5007_; lean_object* v_issues_5008_; lean_object* v_canon_5009_; lean_object* v_instanceOverrides_5010_; uint8_t v_debug_5011_; lean_object* v___x_5013_; uint8_t v_isShared_5014_; uint8_t v_isSharedCheck_5030_; 
v___x_4998_ = lean_st_ref_take(v_a_4996_);
v_share_4999_ = lean_ctor_get(v___x_4998_, 0);
v_maxFVar_5000_ = lean_ctor_get(v___x_4998_, 1);
v_proofInstInfo_5001_ = lean_ctor_get(v___x_4998_, 2);
v_proofInstInfoFVar_5002_ = lean_ctor_get(v___x_4998_, 3);
v_inferType_5003_ = lean_ctor_get(v___x_4998_, 4);
v_getLevel_5004_ = lean_ctor_get(v___x_4998_, 5);
v_congrInfo_5005_ = lean_ctor_get(v___x_4998_, 6);
v_defEqI_5006_ = lean_ctor_get(v___x_4998_, 7);
v_extensions_5007_ = lean_ctor_get(v___x_4998_, 8);
v_issues_5008_ = lean_ctor_get(v___x_4998_, 9);
v_canon_5009_ = lean_ctor_get(v___x_4998_, 10);
v_instanceOverrides_5010_ = lean_ctor_get(v___x_4998_, 11);
v_debug_5011_ = lean_ctor_get_uint8(v___x_4998_, sizeof(void*)*12);
v_isSharedCheck_5030_ = !lean_is_exclusive(v___x_4998_);
if (v_isSharedCheck_5030_ == 0)
{
v___x_5013_ = v___x_4998_;
v_isShared_5014_ = v_isSharedCheck_5030_;
goto v_resetjp_5012_;
}
else
{
lean_inc(v_instanceOverrides_5010_);
lean_inc(v_canon_5009_);
lean_inc(v_issues_5008_);
lean_inc(v_extensions_5007_);
lean_inc(v_defEqI_5006_);
lean_inc(v_congrInfo_5005_);
lean_inc(v_getLevel_5004_);
lean_inc(v_inferType_5003_);
lean_inc(v_proofInstInfoFVar_5002_);
lean_inc(v_proofInstInfo_5001_);
lean_inc(v_maxFVar_5000_);
lean_inc(v_share_4999_);
lean_dec(v___x_4998_);
v___x_5013_ = lean_box(0);
v_isShared_5014_ = v_isSharedCheck_5030_;
goto v_resetjp_5012_;
}
v_resetjp_5012_:
{
lean_object* v_id_5015_; lean_object* v___x_5016_; lean_object* v___y_5018_; lean_object* v___x_5024_; uint8_t v___x_5025_; 
v_id_5015_ = lean_ctor_get(v_ext_4994_, 0);
v___x_5016_ = lean_box(0);
v___x_5024_ = lean_array_get_size(v_extensions_5007_);
v___x_5025_ = lean_nat_dec_lt(v_id_5015_, v___x_5024_);
if (v___x_5025_ == 0)
{
lean_dec(v_f_4995_);
v___y_5018_ = v_extensions_5007_;
goto v___jp_5017_;
}
else
{
lean_object* v_v_5026_; lean_object* v_xs_x27_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; 
v_v_5026_ = lean_array_fget(v_extensions_5007_, v_id_5015_);
v_xs_x27_5027_ = lean_array_fset(v_extensions_5007_, v_id_5015_, v___x_5016_);
v___x_5028_ = lean_apply_1(v_f_4995_, v_v_5026_);
v___x_5029_ = lean_array_fset(v_xs_x27_5027_, v_id_5015_, v___x_5028_);
v___y_5018_ = v___x_5029_;
goto v___jp_5017_;
}
v___jp_5017_:
{
lean_object* v___x_5020_; 
if (v_isShared_5014_ == 0)
{
lean_ctor_set(v___x_5013_, 8, v___y_5018_);
v___x_5020_ = v___x_5013_;
goto v_reusejp_5019_;
}
else
{
lean_object* v_reuseFailAlloc_5023_; 
v_reuseFailAlloc_5023_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_5023_, 0, v_share_4999_);
lean_ctor_set(v_reuseFailAlloc_5023_, 1, v_maxFVar_5000_);
lean_ctor_set(v_reuseFailAlloc_5023_, 2, v_proofInstInfo_5001_);
lean_ctor_set(v_reuseFailAlloc_5023_, 3, v_proofInstInfoFVar_5002_);
lean_ctor_set(v_reuseFailAlloc_5023_, 4, v_inferType_5003_);
lean_ctor_set(v_reuseFailAlloc_5023_, 5, v_getLevel_5004_);
lean_ctor_set(v_reuseFailAlloc_5023_, 6, v_congrInfo_5005_);
lean_ctor_set(v_reuseFailAlloc_5023_, 7, v_defEqI_5006_);
lean_ctor_set(v_reuseFailAlloc_5023_, 8, v___y_5018_);
lean_ctor_set(v_reuseFailAlloc_5023_, 9, v_issues_5008_);
lean_ctor_set(v_reuseFailAlloc_5023_, 10, v_canon_5009_);
lean_ctor_set(v_reuseFailAlloc_5023_, 11, v_instanceOverrides_5010_);
lean_ctor_set_uint8(v_reuseFailAlloc_5023_, sizeof(void*)*12, v_debug_5011_);
v___x_5020_ = v_reuseFailAlloc_5023_;
goto v_reusejp_5019_;
}
v_reusejp_5019_:
{
lean_object* v___x_5021_; lean_object* v___x_5022_; 
v___x_5021_ = lean_st_ref_put(v_a_4996_, v___x_5020_);
v___x_5022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5022_, 0, v___x_5016_);
return v___x_5022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg___boxed(lean_object* v_ext_5031_, lean_object* v_f_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_){
_start:
{
lean_object* v_res_5035_; 
v_res_5035_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_5031_, v_f_5032_, v_a_5033_);
lean_dec(v_a_5033_);
lean_dec_ref(v_ext_5031_);
return v_res_5035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(lean_object* v_00_u03c3_5036_, lean_object* v_ext_5037_, lean_object* v_f_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_, lean_object* v_a_5044_){
_start:
{
lean_object* v___x_5046_; 
v___x_5046_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_5037_, v_f_5038_, v_a_5040_);
return v___x_5046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___boxed(lean_object* v_00_u03c3_5047_, lean_object* v_ext_5048_, lean_object* v_f_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_){
_start:
{
lean_object* v_res_5057_; 
v_res_5057_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(v_00_u03c3_5047_, v_ext_5048_, v_f_5049_, v_a_5050_, v_a_5051_, v_a_5052_, v_a_5053_, v_a_5054_, v_a_5055_);
lean_dec(v_a_5055_);
lean_dec_ref(v_a_5054_);
lean_dec(v_a_5053_);
lean_dec_ref(v_a_5052_);
lean_dec(v_a_5051_);
lean_dec_ref(v_a_5050_);
lean_dec_ref(v_ext_5048_);
return v_res_5057_;
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
