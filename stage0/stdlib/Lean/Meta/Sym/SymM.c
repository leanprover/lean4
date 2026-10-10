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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_));
v___x_57_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_));
v___x_59_ = l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0(v___x_56_, v___x_57_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_60_;
v_res_60_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_();
stack->m_obj
 = v_res_60_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4____boxed(lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_();
return v_res_62_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_116_ = lean_unsigned_to_nat(2410647589u);
v___x_117_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__20_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_118_ = l_Lean_Name_num___override(v___x_117_, v___x_116_);
return v___x_118_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_120_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__22_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_121_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_);
v___x_122_ = l_Lean_Name_str___override(v___x_121_, v___x_120_);
return v___x_122_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__24_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_125_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_);
v___x_126_ = l_Lean_Name_str___override(v___x_125_, v___x_124_);
return v___x_126_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_127_ = lean_unsigned_to_nat(2u);
v___x_128_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_);
v___x_129_ = l_Lean_Name_num___override(v___x_128_, v___x_127_);
return v___x_129_;
}
}
lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_131_; uint8_t v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_131_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_132_ = 0;
v___x_133_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_);
v___x_134_ = l_Lean_registerTraceClass(v___x_131_, v___x_132_, v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_135_;
v_res_135_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_();
stack->m_obj
 = v_res_135_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2____boxed(lean_object* v_a_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_();
return v_res_137_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymExtensionState(void){
_start:
{
lean_object* v___x_141_; lean_object* v_snd_142_; 
v___x_141_ = ((lean_object*)(l_Lean_Meta_Sym_SymExtensionStateSpec));
v_snd_142_ = lean_ctor_get(v___x_141_, 1);
lean_inc(v_snd_142_);
return v_snd_142_;
}
}
lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0(){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0___closed__1));
v___x_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_149_;
v_res_149_ = l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0();
stack->m_obj
 = v_res_149_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0___boxed(lean_object* v___y_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___lam__0();
return v_res_151_;
}
}
lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg(){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___closed__1));
return v___x_157_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_158_;
v_res_158_ = l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg();
stack->m_obj
 = v_res_158_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg___boxed(lean_object* v___dummy_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg();
return v_res_160_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0(void){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Meta_Sym_instInhabitedSymExtension_default___redArg();
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension_default(lean_object* v_00_u03c3_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0, &l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0);
return v___x_163_;
}
}
lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension___redArg(){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0, &l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0);
return v___x_165_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_instInhabitedSymExtension___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_166_;
v_res_166_ = l_Lean_Meta_Sym_instInhabitedSymExtension___redArg();
stack->m_obj
 = v_res_166_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension___redArg___boxed(lean_object* v___dummy_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Meta_Sym_instInhabitedSymExtension___redArg();
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymExtension(lean_object* v_a_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0, &l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0);
return v___x_170_;
}
}
lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_));
v___x_175_ = lean_st_mk_ref(v___x_174_);
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_177_;
v_res_177_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_();
stack->m_obj
 = v_res_177_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2____boxed(lean_object* v_a_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_();
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg(lean_object* v_ext_180_){
_start:
{
lean_inc_ref(v_ext_180_);
return v_ext_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg___boxed(lean_object* v_ext_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg(v_ext_181_);
lean_dec_ref(v_ext_181_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1(lean_object* v_00_u03c3_183_, lean_object* v_ext_184_){
_start:
{
lean_inc_ref(v_ext_184_);
return v_ext_184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___boxed(lean_object* v_00_u03c3_185_, lean_object* v_ext_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1(v_00_u03c3_185_, v_ext_186_);
lean_dec_ref(v_ext_186_);
return v_res_187_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = ((lean_object*)(l_Lean_Meta_Sym_registerSymExtension___redArg___closed__0));
v___x_190_ = lean_mk_io_user_error(v___x_189_);
return v___x_190_;
}
}
lean_object* l_Lean_Meta_Sym_registerSymExtension___redArg(lean_object* v_mkInitial_191_){
_start:
{
uint8_t v___x_193_; 
v___x_193_ = l_Lean_initializing();
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_195_; 
lean_dec_ref(v_mkInitial_191_);
v___x_194_ = lean_obj_once(&l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1, &l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1_once, _init_l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1);
v___x_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
return v___x_195_;
}
else
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_196_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef;
v___x_197_ = lean_st_ref_get(v___x_196_);
v___x_198_ = lean_array_get_size(v___x_197_);
lean_dec(v___x_197_);
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v_mkInitial_191_);
v___x_200_ = lean_st_ref_take(v___x_196_);
lean_inc_ref(v___x_199_);
v___x_201_ = lean_array_push(v___x_200_, v___x_199_);
v___x_202_ = lean_st_ref_put(v___x_196_, v___x_201_);
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_199_);
return v___x_203_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_registerSymExtension___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mkInitial_191_ = stack[0].m_obj;
lean_object* v_res_204_;
v_res_204_ = l_Lean_Meta_Sym_registerSymExtension___redArg(v_mkInitial_191_);
stack->m_obj
 = v_res_204_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension___redArg___boxed(lean_object* v_mkInitial_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_Meta_Sym_registerSymExtension___redArg(v_mkInitial_205_);
return v_res_207_;
}
}
lean_object* l_Lean_Meta_Sym_registerSymExtension(lean_object* v_00_u03c3_208_, lean_object* v_mkInitial_209_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_Meta_Sym_registerSymExtension___redArg(v_mkInitial_209_);
return v___x_211_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_registerSymExtension_0interp(lean_interpreter_value* stack)
{
lean_object* v_mkInitial_209_ = stack[1].m_obj;
lean_object* v_res_212_;
v_res_212_ = l_Lean_Meta_Sym_registerSymExtension(lean_box(0), v_mkInitial_209_);
stack->m_obj
 = v_res_212_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_registerSymExtension___boxed(lean_object* v_00_u03c3_213_, lean_object* v_mkInitial_214_, lean_object* v_a_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_Meta_Sym_registerSymExtension(v_00_u03c3_213_, v_mkInitial_214_);
return v_res_216_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(size_t v_sz_217_, size_t v_i_218_, lean_object* v_bs_219_){
_start:
{
uint8_t v___x_221_; 
v___x_221_ = lean_usize_dec_lt(v_i_218_, v_sz_217_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; 
v___x_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_222_, 0, v_bs_219_);
return v___x_222_;
}
else
{
lean_object* v_v_223_; lean_object* v_mkInitial_224_; lean_object* v___x_225_; lean_object* v_bs_x27_226_; lean_object* v___x_227_; 
v_v_223_ = lean_array_uget_borrowed(v_bs_219_, v_i_218_);
v_mkInitial_224_ = lean_ctor_get(v_v_223_, 1);
lean_inc_ref(v_mkInitial_224_);
v___x_225_ = lean_unsigned_to_nat(0u);
v_bs_x27_226_ = lean_array_uset(v_bs_219_, v_i_218_, v___x_225_);
v___x_227_ = lean_apply_1(v_mkInitial_224_, lean_box(0));
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; size_t v___x_229_; size_t v___x_230_; lean_object* v___x_231_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_a_228_);
lean_dec_ref_known(v___x_227_, 1);
v___x_229_ = ((size_t)1ULL);
v___x_230_ = lean_usize_add(v_i_218_, v___x_229_);
v___x_231_ = lean_array_uset(v_bs_x27_226_, v_i_218_, v_a_228_);
v_i_218_ = v___x_230_;
v_bs_219_ = v___x_231_;
goto _start;
}
else
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
lean_dec_ref(v_bs_x27_226_);
v_a_233_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_227_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_227_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_217_ = stack[0].m_num;
size_t v_i_218_ = stack[1].m_num;
lean_object* v_bs_219_ = stack[2].m_obj;
lean_object* v_res_241_;
v_res_241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(v_sz_217_, v_i_218_, v_bs_219_);
stack->m_obj
 = v_res_241_;
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
lean_object* l_Lean_Meta_Sym_SymExtensions_mkInitialStates(){
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
LEAN_EXPORT void l_Lean_Meta_Sym_SymExtensions_mkInitialStates_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_255_;
v_res_255_ = l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
stack->m_obj
 = v_res_255_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtensions_mkInitialStates___boxed(lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx___impl(lean_object* v_x_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = lean_obj_tag_nat(v_x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorIdx___impl___boxed(lean_object* v_x_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_Meta_Sym_CongrInfo_ctorIdx___impl(v_x_268_);
lean_dec(v_x_268_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(lean_object* v_t_270_, lean_object* v_k_271_){
_start:
{
switch(lean_obj_tag(v_t_270_))
{
case 0:
{
return v_k_271_;
}
case 1:
{
lean_object* v_prefixSize_272_; lean_object* v_suffixSize_273_; lean_object* v___x_274_; 
v_prefixSize_272_ = lean_ctor_get(v_t_270_, 0);
lean_inc(v_prefixSize_272_);
v_suffixSize_273_ = lean_ctor_get(v_t_270_, 1);
lean_inc(v_suffixSize_273_);
lean_dec_ref_known(v_t_270_, 2);
v___x_274_ = lean_apply_2(v_k_271_, v_prefixSize_272_, v_suffixSize_273_);
return v___x_274_;
}
default: 
{
lean_object* v_rewritable_275_; lean_object* v___x_276_; 
v_rewritable_275_ = lean_ctor_get(v_t_270_, 0);
lean_inc_ref(v_rewritable_275_);
lean_dec(v_t_270_);
v___x_276_ = lean_apply_1(v_k_271_, v_rewritable_275_);
return v___x_276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim(lean_object* v_motive_277_, lean_object* v_ctorIdx_278_, lean_object* v_t_279_, lean_object* v_h_280_, lean_object* v_k_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_279_, v_k_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_ctorElim___boxed(lean_object* v_motive_283_, lean_object* v_ctorIdx_284_, lean_object* v_t_285_, lean_object* v_h_286_, lean_object* v_k_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_Meta_Sym_CongrInfo_ctorElim(v_motive_283_, v_ctorIdx_284_, v_t_285_, v_h_286_, v_k_287_);
lean_dec(v_ctorIdx_284_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_none_elim___redArg(lean_object* v_t_289_, lean_object* v_none_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_289_, v_none_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_none_elim(lean_object* v_motive_292_, lean_object* v_t_293_, lean_object* v_h_294_, lean_object* v_none_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_293_, v_none_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim___redArg(lean_object* v_t_297_, lean_object* v_fixedPrefix_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_297_, v_fixedPrefix_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim(lean_object* v_motive_300_, lean_object* v_t_301_, lean_object* v_h_302_, lean_object* v_fixedPrefix_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_301_, v_fixedPrefix_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_interlaced_elim___redArg(lean_object* v_t_305_, lean_object* v_interlaced_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_305_, v_interlaced_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_interlaced_elim(lean_object* v_motive_308_, lean_object* v_t_309_, lean_object* v_h_310_, lean_object* v_interlaced_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_309_, v_interlaced_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim___redArg(lean_object* v_t_313_, lean_object* v_congrTheorem_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_313_, v_congrTheorem_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim(lean_object* v_motive_316_, lean_object* v_t_317_, lean_object* v_h_318_, lean_object* v_congrTheorem_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_317_, v_congrTheorem_319_);
return v___x_320_;
}
}
lean_object* l_Lean_Meta_Sym_unfoldReducibleStep(lean_object* v_e_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_Expr_getAppFn(v_e_327_);
if (lean_obj_tag(v___x_333_) == 4)
{
lean_object* v_declName_334_; lean_object* v___x_335_; lean_object* v_env_336_; uint8_t v___x_337_; 
v_declName_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_declName_334_);
lean_dec_ref_known(v___x_333_, 2);
v___x_335_ = lean_st_ref_get(v_a_331_);
v_env_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc_ref(v_env_336_);
lean_dec(v___x_335_);
v___x_337_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_336_, v_declName_334_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec_ref(v_e_327_);
v___x_338_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
return v___x_339_;
}
else
{
uint8_t v___x_340_; lean_object* v___x_341_; 
v___x_340_ = 0;
v___x_341_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_327_, v___x_340_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_361_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_361_ == 0)
{
v___x_344_ = v___x_341_;
v_isShared_345_ = v_isSharedCheck_361_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_341_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_361_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
if (lean_obj_tag(v_a_342_) == 1)
{
lean_object* v_val_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_356_; 
v_val_346_ = lean_ctor_get(v_a_342_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v_a_342_);
if (v_isSharedCheck_356_ == 0)
{
v___x_348_ = v_a_342_;
v_isShared_349_ = v_isSharedCheck_356_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_val_346_);
lean_dec(v_a_342_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_356_;
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
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_val_346_);
v___x_351_ = v_reuseFailAlloc_355_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_353_; 
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 0, v___x_351_);
v___x_353_ = v___x_344_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
else
{
lean_object* v___x_357_; lean_object* v___x_359_; 
lean_dec(v_a_342_);
v___x_357_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 0, v___x_357_);
v___x_359_ = v___x_344_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
v_a_362_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_341_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_341_);
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
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; 
lean_dec_ref(v___x_333_);
lean_dec_ref(v_e_327_);
v___x_370_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
return v___x_371_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_unfoldReducibleStep_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_327_ = stack[0].m_obj;
lean_object* v_a_328_ = stack[1].m_obj;
lean_object* v_a_329_ = stack[2].m_obj;
lean_object* v_a_330_ = stack[3].m_obj;
lean_object* v_a_331_ = stack[4].m_obj;
lean_object* v_res_372_;
v_res_372_ = l_Lean_Meta_Sym_unfoldReducibleStep(v_e_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
stack->m_obj
 = v_res_372_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducibleStep___boxed(lean_object* v_e_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Meta_Sym_unfoldReducibleStep(v_e_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
return v_res_379_;
}
}
uint8_t l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0(lean_object* v_env_380_, lean_object* v_e_381_){
_start:
{
if (lean_obj_tag(v_e_381_) == 4)
{
lean_object* v_declName_382_; uint8_t v___x_383_; 
v_declName_382_ = lean_ctor_get(v_e_381_, 0);
lean_inc(v_declName_382_);
lean_dec_ref_known(v_e_381_, 2);
v___x_383_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_380_, v_declName_382_);
return v___x_383_;
}
else
{
uint8_t v___x_384_; 
lean_dec_ref(v_e_381_);
lean_dec_ref(v_env_380_);
v___x_384_ = 0;
return v___x_384_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_380_ = stack[0].m_obj;
lean_object* v_e_381_ = stack[1].m_obj;
uint8_t v_res_385_;
v_res_385_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0(v_env_380_, v_e_381_);
stack->m_num = v_res_385_;
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
lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(lean_object* v_e_390_, lean_object* v_a_391_){
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
LEAN_EXPORT void l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_390_ = stack[0].m_obj;
lean_object* v_a_391_ = stack[1].m_obj;
lean_object* v_res_410_;
v_res_410_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_390_, v_a_391_);
stack->m_obj
 = v_res_410_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___boxed(lean_object* v_e_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_411_, v_a_412_);
lean_dec(v_a_412_);
lean_dec_ref(v_e_411_);
return v_res_414_;
}
}
lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget(lean_object* v_e_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_415_, v_a_417_);
return v___x_419_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_isUnfoldReducibleTarget_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_415_ = stack[0].m_obj;
lean_object* v_a_416_ = stack[1].m_obj;
lean_object* v_a_417_ = stack[2].m_obj;
lean_object* v_res_420_;
v_res_420_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget(v_e_415_, v_a_416_, v_a_417_);
stack->m_obj
 = v_res_420_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleTarget___boxed(lean_object* v_e_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget(v_e_421_, v_a_422_, v_a_423_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
lean_dec_ref(v_e_421_);
return v_res_425_;
}
}
lean_object* l_Lean_Meta_Sym_unfoldReducible___lam__0(lean_object* v_e_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v_e_426_);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_unfoldReducible___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_426_ = stack[0].m_obj;
lean_object* v___y_427_ = stack[1].m_obj;
lean_object* v___y_428_ = stack[2].m_obj;
lean_object* v___y_429_ = stack[3].m_obj;
lean_object* v___y_430_ = stack[4].m_obj;
lean_object* v_res_434_;
v_res_434_ = l_Lean_Meta_Sym_unfoldReducible___lam__0(v_e_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
stack->m_obj
 = v_res_434_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___lam__0___boxed(lean_object* v_e_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_Meta_Sym_unfoldReducible___lam__0(v_e_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
return v_res_441_;
}
}
lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_object* v_00_u03b1_442_, lean_object* v_x_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_apply_1(v_x_443_, lean_box(0));
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT void l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_443_ = stack[1].m_obj;
lean_object* v___y_444_ = stack[2].m_obj;
lean_object* v___y_445_ = stack[3].m_obj;
lean_object* v___y_446_ = stack[4].m_obj;
lean_object* v___y_447_ = stack[5].m_obj;
lean_object* v_res_451_;
v_res_451_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v_x_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
stack->m_obj
 = v_res_451_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0___boxed(lean_object* v_00_u03b1_452_, lean_object* v_x_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(v_00_u03b1_452_, v_x_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
return v_res_459_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(lean_object* v_a_460_, lean_object* v_x_461_){
_start:
{
if (lean_obj_tag(v_x_461_) == 0)
{
uint8_t v___x_462_; 
v___x_462_ = 0;
return v___x_462_;
}
else
{
lean_object* v_key_463_; lean_object* v_tail_464_; uint8_t v___x_465_; 
v_key_463_ = lean_ctor_get(v_x_461_, 0);
v_tail_464_ = lean_ctor_get(v_x_461_, 2);
v___x_465_ = l_Lean_ExprStructEq_beq(v_key_463_, v_a_460_);
if (v___x_465_ == 0)
{
v_x_461_ = v_tail_464_;
goto _start;
}
else
{
return v___x_465_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_460_ = stack[0].m_obj;
lean_object* v_x_461_ = stack[1].m_obj;
uint8_t v_res_467_;
v_res_467_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_460_, v_x_461_);
stack->m_num = v_res_467_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object* v_a_468_, lean_object* v_x_469_){
_start:
{
uint8_t v_res_470_; lean_object* v_r_471_; 
v_res_470_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_468_, v_x_469_);
lean_dec(v_x_469_);
lean_dec_ref(v_a_468_);
v_r_471_ = lean_box(v_res_470_);
return v_r_471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object* v_x_472_, lean_object* v_x_473_){
_start:
{
if (lean_obj_tag(v_x_473_) == 0)
{
return v_x_472_;
}
else
{
lean_object* v_key_474_; lean_object* v_value_475_; lean_object* v_tail_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_499_; 
v_key_474_ = lean_ctor_get(v_x_473_, 0);
v_value_475_ = lean_ctor_get(v_x_473_, 1);
v_tail_476_ = lean_ctor_get(v_x_473_, 2);
v_isSharedCheck_499_ = !lean_is_exclusive(v_x_473_);
if (v_isSharedCheck_499_ == 0)
{
v___x_478_ = v_x_473_;
v_isShared_479_ = v_isSharedCheck_499_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_tail_476_);
lean_inc(v_value_475_);
lean_inc(v_key_474_);
lean_dec(v_x_473_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_499_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; uint64_t v___x_481_; uint64_t v___x_482_; uint64_t v___x_483_; uint64_t v_fold_484_; uint64_t v___x_485_; uint64_t v___x_486_; uint64_t v___x_487_; size_t v___x_488_; size_t v___x_489_; size_t v___x_490_; size_t v___x_491_; size_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_480_ = lean_array_get_size(v_x_472_);
v___x_481_ = l_Lean_ExprStructEq_hash(v_key_474_);
v___x_482_ = 32ULL;
v___x_483_ = lean_uint64_shift_right(v___x_481_, v___x_482_);
v_fold_484_ = lean_uint64_xor(v___x_481_, v___x_483_);
v___x_485_ = 16ULL;
v___x_486_ = lean_uint64_shift_right(v_fold_484_, v___x_485_);
v___x_487_ = lean_uint64_xor(v_fold_484_, v___x_486_);
v___x_488_ = lean_uint64_to_usize(v___x_487_);
v___x_489_ = lean_usize_of_nat(v___x_480_);
v___x_490_ = ((size_t)1ULL);
v___x_491_ = lean_usize_sub(v___x_489_, v___x_490_);
v___x_492_ = lean_usize_land(v___x_488_, v___x_491_);
v___x_493_ = lean_array_uget_borrowed(v_x_472_, v___x_492_);
lean_inc(v___x_493_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 2, v___x_493_);
v___x_495_ = v___x_478_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_key_474_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_value_475_);
lean_ctor_set(v_reuseFailAlloc_498_, 2, v___x_493_);
v___x_495_ = v_reuseFailAlloc_498_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
lean_object* v___x_496_; 
v___x_496_ = lean_array_uset(v_x_472_, v___x_492_, v___x_495_);
v_x_472_ = v___x_496_;
v_x_473_ = v_tail_476_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object* v_i_500_, lean_object* v_source_501_, lean_object* v_target_502_){
_start:
{
lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_503_ = lean_array_get_size(v_source_501_);
v___x_504_ = lean_nat_dec_lt(v_i_500_, v___x_503_);
if (v___x_504_ == 0)
{
lean_dec_ref(v_source_501_);
lean_dec(v_i_500_);
return v_target_502_;
}
else
{
lean_object* v_es_505_; lean_object* v___x_506_; lean_object* v_source_507_; lean_object* v_target_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v_es_505_ = lean_array_fget(v_source_501_, v_i_500_);
v___x_506_ = lean_box(0);
v_source_507_ = lean_array_fset(v_source_501_, v_i_500_, v___x_506_);
v_target_508_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_502_, v_es_505_);
v___x_509_ = lean_unsigned_to_nat(1u);
v___x_510_ = lean_nat_add(v_i_500_, v___x_509_);
lean_dec(v_i_500_);
v_i_500_ = v___x_510_;
v_source_501_ = v_source_507_;
v_target_502_ = v_target_508_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(lean_object* v_data_512_){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v_nbuckets_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_513_ = lean_array_get_size(v_data_512_);
v___x_514_ = lean_unsigned_to_nat(2u);
v_nbuckets_515_ = lean_nat_mul(v___x_513_, v___x_514_);
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = lean_box(0);
v___x_518_ = lean_mk_array(v_nbuckets_515_, v___x_517_);
v___x_519_ = lean_array_propagate_mark(v_data_512_, v___x_518_);
v___x_520_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_516_, v_data_512_, v___x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(lean_object* v_a_521_, lean_object* v_b_522_, lean_object* v_x_523_){
_start:
{
if (lean_obj_tag(v_x_523_) == 0)
{
lean_dec(v_b_522_);
lean_dec_ref(v_a_521_);
return v_x_523_;
}
else
{
lean_object* v_key_524_; lean_object* v_value_525_; lean_object* v_tail_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_538_; 
v_key_524_ = lean_ctor_get(v_x_523_, 0);
v_value_525_ = lean_ctor_get(v_x_523_, 1);
v_tail_526_ = lean_ctor_get(v_x_523_, 2);
v_isSharedCheck_538_ = !lean_is_exclusive(v_x_523_);
if (v_isSharedCheck_538_ == 0)
{
v___x_528_ = v_x_523_;
v_isShared_529_ = v_isSharedCheck_538_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_tail_526_);
lean_inc(v_value_525_);
lean_inc(v_key_524_);
lean_dec(v_x_523_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_538_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
uint8_t v___x_530_; 
v___x_530_ = l_Lean_ExprStructEq_beq(v_key_524_, v_a_521_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_531_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_521_, v_b_522_, v_tail_526_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 2, v___x_531_);
v___x_533_ = v___x_528_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_key_524_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_value_525_);
lean_ctor_set(v_reuseFailAlloc_534_, 2, v___x_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
else
{
lean_object* v___x_536_; 
lean_dec(v_value_525_);
lean_dec(v_key_524_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 1, v_b_522_);
lean_ctor_set(v___x_528_, 0, v_a_521_);
v___x_536_ = v___x_528_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_521_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v_b_522_);
lean_ctor_set(v_reuseFailAlloc_537_, 2, v_tail_526_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(lean_object* v_m_539_, lean_object* v_a_540_, lean_object* v_b_541_){
_start:
{
lean_object* v_size_542_; lean_object* v_buckets_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_586_; 
v_size_542_ = lean_ctor_get(v_m_539_, 0);
v_buckets_543_ = lean_ctor_get(v_m_539_, 1);
v_isSharedCheck_586_ = !lean_is_exclusive(v_m_539_);
if (v_isSharedCheck_586_ == 0)
{
v___x_545_ = v_m_539_;
v_isShared_546_ = v_isSharedCheck_586_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_buckets_543_);
lean_inc(v_size_542_);
lean_dec(v_m_539_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_586_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; uint64_t v___x_548_; uint64_t v___x_549_; uint64_t v___x_550_; uint64_t v_fold_551_; uint64_t v___x_552_; uint64_t v___x_553_; uint64_t v___x_554_; size_t v___x_555_; size_t v___x_556_; size_t v___x_557_; size_t v___x_558_; size_t v___x_559_; lean_object* v_bkt_560_; uint8_t v___x_561_; 
v___x_547_ = lean_array_get_size(v_buckets_543_);
v___x_548_ = l_Lean_ExprStructEq_hash(v_a_540_);
v___x_549_ = 32ULL;
v___x_550_ = lean_uint64_shift_right(v___x_548_, v___x_549_);
v_fold_551_ = lean_uint64_xor(v___x_548_, v___x_550_);
v___x_552_ = 16ULL;
v___x_553_ = lean_uint64_shift_right(v_fold_551_, v___x_552_);
v___x_554_ = lean_uint64_xor(v_fold_551_, v___x_553_);
v___x_555_ = lean_uint64_to_usize(v___x_554_);
v___x_556_ = lean_usize_of_nat(v___x_547_);
v___x_557_ = ((size_t)1ULL);
v___x_558_ = lean_usize_sub(v___x_556_, v___x_557_);
v___x_559_ = lean_usize_land(v___x_555_, v___x_558_);
v_bkt_560_ = lean_array_uget_borrowed(v_buckets_543_, v___x_559_);
v___x_561_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_540_, v_bkt_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v_size_x27_563_; lean_object* v___x_564_; lean_object* v_buckets_x27_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_562_ = lean_unsigned_to_nat(1u);
v_size_x27_563_ = lean_nat_add(v_size_542_, v___x_562_);
lean_dec(v_size_542_);
lean_inc(v_bkt_560_);
v___x_564_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_564_, 0, v_a_540_);
lean_ctor_set(v___x_564_, 1, v_b_541_);
lean_ctor_set(v___x_564_, 2, v_bkt_560_);
v_buckets_x27_565_ = lean_array_uset(v_buckets_543_, v___x_559_, v___x_564_);
v___x_566_ = lean_unsigned_to_nat(4u);
v___x_567_ = lean_nat_mul(v_size_x27_563_, v___x_566_);
v___x_568_ = lean_unsigned_to_nat(3u);
v___x_569_ = lean_nat_div(v___x_567_, v___x_568_);
lean_dec(v___x_567_);
v___x_570_ = lean_array_get_size(v_buckets_x27_565_);
v___x_571_ = lean_nat_dec_le(v___x_569_, v___x_570_);
lean_dec(v___x_569_);
if (v___x_571_ == 0)
{
lean_object* v_val_572_; lean_object* v___x_574_; 
v_val_572_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_565_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 1, v_val_572_);
lean_ctor_set(v___x_545_, 0, v_size_x27_563_);
v___x_574_ = v___x_545_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_size_x27_563_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_val_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
else
{
lean_object* v___x_577_; 
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 1, v_buckets_x27_565_);
lean_ctor_set(v___x_545_, 0, v_size_x27_563_);
v___x_577_ = v___x_545_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_size_x27_563_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_buckets_x27_565_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
else
{
lean_object* v___x_579_; lean_object* v_buckets_x27_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_584_; 
lean_inc(v_bkt_560_);
v___x_579_ = lean_box(0);
v_buckets_x27_580_ = lean_array_uset(v_buckets_543_, v___x_559_, v___x_579_);
v___x_581_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_540_, v_b_541_, v_bkt_560_);
v___x_582_ = lean_array_uset(v_buckets_x27_580_, v___x_559_, v___x_581_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 1, v___x_582_);
v___x_584_ = v___x_545_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_size_542_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(lean_object* v_a_587_, lean_object* v_e_588_, lean_object* v_a_589_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_591_ = lean_st_ref_take(v_a_587_);
v___x_592_ = lean_box(0);
v___x_593_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v___x_591_, v_e_588_, v_a_589_);
v___x_594_ = lean_st_ref_put(v_a_587_, v___x_593_);
return v___x_592_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_587_ = stack[0].m_obj;
lean_object* v_e_588_ = stack[1].m_obj;
lean_object* v_a_589_ = stack[2].m_obj;
lean_object* v_res_595_;
v_res_595_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(v_a_587_, v_e_588_, v_a_589_);
stack->m_obj
 = v_res_595_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed(lean_object* v_a_596_, lean_object* v_e_597_, lean_object* v_a_598_, lean_object* v___y_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(v_a_596_, v_e_597_, v_a_598_);
lean_dec(v_a_596_);
return v_res_600_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = l_Lean_maxRecDepthErrorMessage;
v___x_607_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
return v___x_607_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
v___x_609_ = l_Lean_MessageData_ofFormat(v___x_608_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_610_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
v___x_611_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2));
v___x_612_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v___x_610_);
return v___x_612_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(lean_object* v_ref_613_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_615_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_616_, 0, v_ref_613_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_613_ = stack[0].m_obj;
lean_object* v_res_618_;
v_res_618_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_613_);
stack->m_obj
 = v_res_618_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object* v_ref_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_619_);
return v_res_621_;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(lean_object* v_x_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v___y_630_; lean_object* v_toCold_639_; lean_object* v_currRecDepth_640_; lean_object* v_ref_641_; uint16_t v_optionFlags_642_; uint8_t v_suppressElabErrors_643_; uint8_t v_isRecordingDeps_644_; lean_object* v_maxRecDepth_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v_toCold_639_ = lean_ctor_get(v___y_626_, 0);
v_currRecDepth_640_ = lean_ctor_get(v___y_626_, 1);
v_ref_641_ = lean_ctor_get(v___y_626_, 2);
v_optionFlags_642_ = lean_ctor_get_uint16(v___y_626_, sizeof(void*)*3);
v_suppressElabErrors_643_ = lean_ctor_get_uint8(v___y_626_, sizeof(void*)*3 + 2);
v_isRecordingDeps_644_ = lean_ctor_get_uint8(v___y_626_, sizeof(void*)*3 + 3);
v_maxRecDepth_650_ = lean_ctor_get(v_toCold_639_, 3);
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_nat_dec_eq(v_maxRecDepth_650_, v___x_651_);
if (v___x_652_ == 0)
{
uint8_t v___x_653_; 
v___x_653_ = lean_nat_dec_eq(v_currRecDepth_640_, v_maxRecDepth_650_);
if (v___x_653_ == 0)
{
goto v___jp_645_;
}
else
{
lean_object* v___x_654_; 
lean_dec_ref(v_x_622_);
lean_inc(v_ref_641_);
v___x_654_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_641_);
v___y_630_ = v___x_654_;
goto v___jp_629_;
}
}
else
{
goto v___jp_645_;
}
v___jp_629_:
{
if (lean_obj_tag(v___y_630_) == 0)
{
return v___y_630_;
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
v_a_631_ = lean_ctor_get(v___y_630_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___y_630_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___y_630_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___y_630_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
v___jp_645_:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_646_ = lean_unsigned_to_nat(1u);
v___x_647_ = lean_nat_add(v_currRecDepth_640_, v___x_646_);
lean_inc(v_ref_641_);
lean_inc_ref(v_toCold_639_);
v___x_648_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_648_, 0, v_toCold_639_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
lean_ctor_set(v___x_648_, 2, v_ref_641_);
lean_ctor_set_uint16(v___x_648_, sizeof(void*)*3, v_optionFlags_642_);
lean_ctor_set_uint8(v___x_648_, sizeof(void*)*3 + 2, v_suppressElabErrors_643_);
lean_ctor_set_uint8(v___x_648_, sizeof(void*)*3 + 3, v_isRecordingDeps_644_);
lean_inc(v___y_627_);
lean_inc(v___y_625_);
lean_inc_ref(v___y_624_);
lean_inc(v___y_623_);
v___x_649_ = lean_apply_6(v_x_622_, v___y_623_, v___y_624_, v___y_625_, v___x_648_, v___y_627_, lean_box(0));
v___y_630_ = v___x_649_;
goto v___jp_629_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_622_ = stack[0].m_obj;
lean_object* v___y_623_ = stack[1].m_obj;
lean_object* v___y_624_ = stack[2].m_obj;
lean_object* v___y_625_ = stack[3].m_obj;
lean_object* v___y_626_ = stack[4].m_obj;
lean_object* v___y_627_ = stack[5].m_obj;
lean_object* v_res_655_;
v_res_655_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
stack->m_obj
 = v_res_655_;
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
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_664_, lean_object* v_x_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_apply_1(v_x_665_, lean_box(0));
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_665_ = stack[1].m_obj;
lean_object* v___y_666_ = stack[2].m_obj;
lean_object* v___y_667_ = stack[3].m_obj;
lean_object* v___y_668_ = stack[4].m_obj;
lean_object* v___y_669_ = stack[5].m_obj;
lean_object* v_res_673_;
v_res_673_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v_x_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
stack->m_obj
 = v_res_673_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_674_, lean_object* v_x_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(v_00_u03b1_674_, v_x_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_a_682_, lean_object* v_x_683_){
_start:
{
if (lean_obj_tag(v_x_683_) == 0)
{
lean_object* v___x_684_; 
v___x_684_ = lean_box(0);
return v___x_684_;
}
else
{
lean_object* v_key_685_; lean_object* v_value_686_; lean_object* v_tail_687_; uint8_t v___x_688_; 
v_key_685_ = lean_ctor_get(v_x_683_, 0);
v_value_686_ = lean_ctor_get(v_x_683_, 1);
v_tail_687_ = lean_ctor_get(v_x_683_, 2);
v___x_688_ = l_Lean_ExprStructEq_beq(v_key_685_, v_a_682_);
if (v___x_688_ == 0)
{
v_x_683_ = v_tail_687_;
goto _start;
}
else
{
lean_object* v___x_690_; 
lean_inc(v_value_686_);
v___x_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_690_, 0, v_value_686_);
return v___x_690_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_a_691_, lean_object* v_x_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_691_, v_x_692_);
lean_dec(v_x_692_);
lean_dec_ref(v_a_691_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(lean_object* v_m_694_, lean_object* v_a_695_){
_start:
{
lean_object* v_buckets_696_; lean_object* v___x_697_; uint64_t v___x_698_; uint64_t v___x_699_; uint64_t v___x_700_; uint64_t v_fold_701_; uint64_t v___x_702_; uint64_t v___x_703_; uint64_t v___x_704_; size_t v___x_705_; size_t v___x_706_; size_t v___x_707_; size_t v___x_708_; size_t v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v_buckets_696_ = lean_ctor_get(v_m_694_, 1);
v___x_697_ = lean_array_get_size(v_buckets_696_);
v___x_698_ = l_Lean_ExprStructEq_hash(v_a_695_);
v___x_699_ = 32ULL;
v___x_700_ = lean_uint64_shift_right(v___x_698_, v___x_699_);
v_fold_701_ = lean_uint64_xor(v___x_698_, v___x_700_);
v___x_702_ = 16ULL;
v___x_703_ = lean_uint64_shift_right(v_fold_701_, v___x_702_);
v___x_704_ = lean_uint64_xor(v_fold_701_, v___x_703_);
v___x_705_ = lean_uint64_to_usize(v___x_704_);
v___x_706_ = lean_usize_of_nat(v___x_697_);
v___x_707_ = ((size_t)1ULL);
v___x_708_ = lean_usize_sub(v___x_706_, v___x_707_);
v___x_709_ = lean_usize_land(v___x_705_, v___x_708_);
v___x_710_ = lean_array_uget_borrowed(v_buckets_696_, v___x_709_);
v___x_711_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_695_, v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_m_712_, lean_object* v_a_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_m_712_, v_a_713_);
lean_dec_ref(v_a_713_);
lean_dec_ref(v_m_712_);
return v_res_714_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(lean_object* v___x_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_715_);
return v___x_721_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_715_ = stack[0].m_obj;
lean_object* v___y_716_ = stack[1].m_obj;
lean_object* v___y_717_ = stack[2].m_obj;
lean_object* v___y_718_ = stack[3].m_obj;
lean_object* v___y_719_ = stack[4].m_obj;
lean_object* v_res_722_;
v_res_722_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(v___x_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
stack->m_obj
 = v_res_722_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object* v___x_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(v___x_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
return v_res_729_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object* v_k_730_, lean_object* v___y_731_, lean_object* v_b_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_738_; 
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
lean_inc(v___y_734_);
lean_inc_ref(v___y_733_);
lean_inc(v___y_731_);
v___x_738_ = lean_apply_7(v_k_730_, v_b_732_, v___y_731_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, lean_box(0));
return v___x_738_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_730_ = stack[0].m_obj;
lean_object* v___y_731_ = stack[1].m_obj;
lean_object* v_b_732_ = stack[2].m_obj;
lean_object* v___y_733_ = stack[3].m_obj;
lean_object* v___y_734_ = stack[4].m_obj;
lean_object* v___y_735_ = stack[5].m_obj;
lean_object* v___y_736_ = stack[6].m_obj;
lean_object* v_res_739_;
v_res_739_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_730_, v___y_731_, v_b_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
stack->m_obj
 = v_res_739_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_740_, lean_object* v___y_741_, lean_object* v_b_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_740_, v___y_741_, v_b_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_741_);
return v_res_748_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_name_749_, uint8_t v_bi_750_, lean_object* v_type_751_, lean_object* v_k_752_, uint8_t v_kind_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___f_760_; lean_object* v___x_761_; 
lean_inc(v___y_754_);
v___f_760_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_760_, 0, v_k_752_);
lean_closure_set(v___f_760_, 1, v___y_754_);
v___x_761_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_749_, v_bi_750_, v_type_751_, v___f_760_, v_kind_753_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
if (lean_obj_tag(v___x_761_) == 0)
{
return v___x_761_;
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_761_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_749_ = stack[0].m_obj;
uint8_t v_bi_750_ = stack[1].m_num;
lean_object* v_type_751_ = stack[2].m_obj;
lean_object* v_k_752_ = stack[3].m_obj;
uint8_t v_kind_753_ = stack[4].m_num;
lean_object* v___y_754_ = stack[5].m_obj;
lean_object* v___y_755_ = stack[6].m_obj;
lean_object* v___y_756_ = stack[7].m_obj;
lean_object* v___y_757_ = stack[8].m_obj;
lean_object* v___y_758_ = stack[9].m_obj;
lean_object* v_res_770_;
v_res_770_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_749_, v_bi_750_, v_type_751_, v_k_752_, v_kind_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
stack->m_obj
 = v_res_770_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_name_771_, lean_object* v_bi_772_, lean_object* v_type_773_, lean_object* v_k_774_, lean_object* v_kind_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
uint8_t v_bi_boxed_782_; uint8_t v_kind_boxed_783_; lean_object* v_res_784_; 
v_bi_boxed_782_ = lean_unbox(v_bi_772_);
v_kind_boxed_783_ = lean_unbox(v_kind_775_);
v_res_784_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_771_, v_bi_boxed_782_, v_type_773_, v_k_774_, v_kind_boxed_783_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
return v_res_784_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(lean_object* v_name_785_, lean_object* v_type_786_, lean_object* v_val_787_, lean_object* v_k_788_, uint8_t v_nondep_789_, uint8_t v_kind_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___f_797_; lean_object* v___x_798_; 
lean_inc(v___y_791_);
v___f_797_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_797_, 0, v_k_788_);
lean_closure_set(v___f_797_, 1, v___y_791_);
v___x_798_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_785_, v_type_786_, v_val_787_, v___f_797_, v_nondep_789_, v_kind_790_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
if (lean_obj_tag(v___x_798_) == 0)
{
return v___x_798_;
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_798_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_798_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_785_ = stack[0].m_obj;
lean_object* v_type_786_ = stack[1].m_obj;
lean_object* v_val_787_ = stack[2].m_obj;
lean_object* v_k_788_ = stack[3].m_obj;
uint8_t v_nondep_789_ = stack[4].m_num;
uint8_t v_kind_790_ = stack[5].m_num;
lean_object* v___y_791_ = stack[6].m_obj;
lean_object* v___y_792_ = stack[7].m_obj;
lean_object* v___y_793_ = stack[8].m_obj;
lean_object* v___y_794_ = stack[9].m_obj;
lean_object* v___y_795_ = stack[10].m_obj;
lean_object* v_res_807_;
v_res_807_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_785_, v_type_786_, v_val_787_, v_k_788_, v_nondep_789_, v_kind_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
stack->m_obj
 = v_res_807_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object* v_name_808_, lean_object* v_type_809_, lean_object* v_val_810_, lean_object* v_k_811_, lean_object* v_nondep_812_, lean_object* v_kind_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
uint8_t v_nondep_boxed_820_; uint8_t v_kind_boxed_821_; lean_object* v_res_822_; 
v_nondep_boxed_820_ = lean_unbox(v_nondep_812_);
v_kind_boxed_821_ = lean_unbox(v_kind_813_);
v_res_822_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_808_, v_type_809_, v_val_810_, v_k_811_, v_nondep_boxed_820_, v_kind_boxed_821_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed(lean_object* v_fvars_823_, lean_object* v_pre_824_, lean_object* v_post_825_, lean_object* v_usedLetOnly_826_, lean_object* v_skipConstInApp_827_, lean_object* v_skipInstances_828_, lean_object* v_body_829_, lean_object* v_x_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
uint8_t v_usedLetOnly_boxed_837_; uint8_t v_skipConstInApp_boxed_838_; uint8_t v_skipInstances_boxed_839_; lean_object* v_res_840_; 
v_usedLetOnly_boxed_837_ = lean_unbox(v_usedLetOnly_826_);
v_skipConstInApp_boxed_838_ = lean_unbox(v_skipConstInApp_827_);
v_skipInstances_boxed_839_ = lean_unbox(v_skipInstances_828_);
v_res_840_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(v_fvars_823_, v_pre_824_, v_post_825_, v_usedLetOnly_boxed_837_, v_skipConstInApp_boxed_838_, v_skipInstances_boxed_839_, v_body_829_, v_x_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
return v_res_840_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(lean_object* v_fvars_844_, lean_object* v_pre_845_, lean_object* v_post_846_, uint8_t v_usedLetOnly_847_, uint8_t v_skipConstInApp_848_, uint8_t v_skipInstances_849_, lean_object* v_body_850_, lean_object* v_x_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = lean_array_push(v_fvars_844_, v_x_851_);
v___x_859_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_845_, v_post_846_, v_usedLetOnly_847_, v_skipConstInApp_848_, v_skipInstances_849_, v___x_858_, v_body_850_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
return v___x_859_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_844_ = stack[0].m_obj;
lean_object* v_pre_845_ = stack[1].m_obj;
lean_object* v_post_846_ = stack[2].m_obj;
uint8_t v_usedLetOnly_847_ = stack[3].m_num;
uint8_t v_skipConstInApp_848_ = stack[4].m_num;
uint8_t v_skipInstances_849_ = stack[5].m_num;
lean_object* v_body_850_ = stack[6].m_obj;
lean_object* v_x_851_ = stack[7].m_obj;
lean_object* v___y_852_ = stack[8].m_obj;
lean_object* v___y_853_ = stack[9].m_obj;
lean_object* v___y_854_ = stack[10].m_obj;
lean_object* v___y_855_ = stack[11].m_obj;
lean_object* v___y_856_ = stack[12].m_obj;
lean_object* v_res_860_;
v_res_860_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(v_fvars_844_, v_pre_845_, v_post_846_, v_usedLetOnly_847_, v_skipConstInApp_848_, v_skipInstances_849_, v_body_850_, v_x_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
stack->m_obj
 = v_res_860_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed(lean_object* v_fvars_861_, lean_object* v_pre_862_, lean_object* v_post_863_, lean_object* v_usedLetOnly_864_, lean_object* v_skipConstInApp_865_, lean_object* v_skipInstances_866_, lean_object* v_body_867_, lean_object* v_x_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
uint8_t v_usedLetOnly_boxed_875_; uint8_t v_skipConstInApp_boxed_876_; uint8_t v_skipInstances_boxed_877_; lean_object* v_res_878_; 
v_usedLetOnly_boxed_875_ = lean_unbox(v_usedLetOnly_864_);
v_skipConstInApp_boxed_876_ = lean_unbox(v_skipConstInApp_865_);
v_skipInstances_boxed_877_ = lean_unbox(v_skipInstances_866_);
v_res_878_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(v_fvars_861_, v_pre_862_, v_post_863_, v_usedLetOnly_boxed_875_, v_skipConstInApp_boxed_876_, v_skipInstances_boxed_877_, v_body_867_, v_x_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
return v_res_878_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(lean_object* v_pre_879_, lean_object* v_post_880_, uint8_t v_usedLetOnly_881_, uint8_t v_skipConstInApp_882_, uint8_t v_skipInstances_883_, lean_object* v_e_884_, lean_object* v_a_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; 
lean_inc_ref(v_post_880_);
lean_inc(v___y_889_);
lean_inc_ref(v___y_888_);
lean_inc(v___y_887_);
lean_inc_ref(v___y_886_);
lean_inc_ref(v_e_884_);
v___x_891_ = lean_apply_6(v_post_880_, v_e_884_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, lean_box(0));
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_910_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_910_ == 0)
{
v___x_894_ = v___x_891_;
v_isShared_895_ = v_isSharedCheck_910_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_910_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
switch(lean_obj_tag(v_a_892_))
{
case 0:
{
lean_object* v_e_896_; lean_object* v___x_898_; 
lean_dec_ref(v_e_884_);
lean_dec_ref(v_post_880_);
lean_dec_ref(v_pre_879_);
v_e_896_ = lean_ctor_get(v_a_892_, 0);
lean_inc_ref(v_e_896_);
lean_dec_ref_known(v_a_892_, 1);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v_e_896_);
v___x_898_ = v___x_894_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_e_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
case 1:
{
lean_object* v_e_900_; lean_object* v___x_901_; 
lean_del_object(v___x_894_);
lean_dec_ref(v_e_884_);
v_e_900_ = lean_ctor_get(v_a_892_, 0);
lean_inc_ref(v_e_900_);
lean_dec_ref_known(v_a_892_, 1);
v___x_901_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_879_, v_post_880_, v_usedLetOnly_881_, v_skipConstInApp_882_, v_skipInstances_883_, v_e_900_, v_a_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
return v___x_901_;
}
default: 
{
lean_object* v_e_x3f_902_; 
lean_dec_ref(v_post_880_);
lean_dec_ref(v_pre_879_);
v_e_x3f_902_ = lean_ctor_get(v_a_892_, 0);
lean_inc(v_e_x3f_902_);
lean_dec_ref_known(v_a_892_, 1);
if (lean_obj_tag(v_e_x3f_902_) == 0)
{
lean_object* v___x_904_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v_e_884_);
v___x_904_ = v___x_894_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_e_884_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
else
{
lean_object* v_val_906_; lean_object* v___x_908_; 
lean_dec_ref(v_e_884_);
v_val_906_ = lean_ctor_get(v_e_x3f_902_, 0);
lean_inc(v_val_906_);
lean_dec_ref_known(v_e_x3f_902_, 1);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v_val_906_);
v___x_908_ = v___x_894_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_val_906_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec_ref(v_e_884_);
lean_dec_ref(v_post_880_);
lean_dec_ref(v_pre_879_);
v_a_911_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_891_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_891_);
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
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_879_ = stack[0].m_obj;
lean_object* v_post_880_ = stack[1].m_obj;
uint8_t v_usedLetOnly_881_ = stack[2].m_num;
uint8_t v_skipConstInApp_882_ = stack[3].m_num;
uint8_t v_skipInstances_883_ = stack[4].m_num;
lean_object* v_e_884_ = stack[5].m_obj;
lean_object* v_a_885_ = stack[6].m_obj;
lean_object* v___y_886_ = stack[7].m_obj;
lean_object* v___y_887_ = stack[8].m_obj;
lean_object* v___y_888_ = stack[9].m_obj;
lean_object* v___y_889_ = stack[10].m_obj;
lean_object* v_res_919_;
v_res_919_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_879_, v_post_880_, v_usedLetOnly_881_, v_skipConstInApp_882_, v_skipInstances_883_, v_e_884_, v_a_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
stack->m_obj
 = v_res_919_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(lean_object* v_pre_920_, lean_object* v_post_921_, uint8_t v_usedLetOnly_922_, uint8_t v_skipConstInApp_923_, uint8_t v_skipInstances_924_, lean_object* v_fvars_925_, lean_object* v_e_926_, lean_object* v_a_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
if (lean_obj_tag(v_e_926_) == 6)
{
lean_object* v_binderName_933_; lean_object* v_binderType_934_; lean_object* v_body_935_; uint8_t v_binderInfo_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___f_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v_binderName_933_ = lean_ctor_get(v_e_926_, 0);
lean_inc(v_binderName_933_);
v_binderType_934_ = lean_ctor_get(v_e_926_, 1);
lean_inc_ref(v_binderType_934_);
v_body_935_ = lean_ctor_get(v_e_926_, 2);
lean_inc_ref(v_body_935_);
v_binderInfo_936_ = lean_ctor_get_uint8(v_e_926_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_926_, 3);
v___x_937_ = lean_box(v_usedLetOnly_922_);
v___x_938_ = lean_box(v_skipConstInApp_923_);
v___x_939_ = lean_box(v_skipInstances_924_);
lean_inc_ref(v_post_921_);
lean_inc_ref(v_pre_920_);
lean_inc_ref(v_fvars_925_);
v___f_940_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_940_, 0, v_fvars_925_);
lean_closure_set(v___f_940_, 1, v_pre_920_);
lean_closure_set(v___f_940_, 2, v_post_921_);
lean_closure_set(v___f_940_, 3, v___x_937_);
lean_closure_set(v___f_940_, 4, v___x_938_);
lean_closure_set(v___f_940_, 5, v___x_939_);
lean_closure_set(v___f_940_, 6, v_body_935_);
v___x_941_ = lean_expr_instantiate_rev(v_binderType_934_, v_fvars_925_);
lean_dec_ref(v_fvars_925_);
lean_dec_ref(v_binderType_934_);
v___x_942_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_920_, v_post_921_, v_usedLetOnly_922_, v_skipConstInApp_923_, v_skipInstances_924_, v___x_941_, v_a_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; uint8_t v___x_944_; lean_object* v___x_945_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_a_943_);
lean_dec_ref_known(v___x_942_, 1);
v___x_944_ = 0;
v___x_945_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_933_, v_binderInfo_936_, v_a_943_, v___f_940_, v___x_944_, v_a_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
return v___x_945_;
}
else
{
lean_dec_ref(v___f_940_);
lean_dec(v_binderName_933_);
return v___x_942_;
}
}
else
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = lean_expr_instantiate_rev(v_e_926_, v_fvars_925_);
lean_dec_ref(v_e_926_);
lean_inc_ref(v_post_921_);
lean_inc_ref(v_pre_920_);
v___x_947_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_920_, v_post_921_, v_usedLetOnly_922_, v_skipConstInApp_923_, v_skipInstances_924_, v___x_946_, v_a_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; uint8_t v___x_949_; uint8_t v___x_950_; uint8_t v___x_951_; lean_object* v___x_952_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_a_948_);
lean_dec_ref_known(v___x_947_, 1);
v___x_949_ = 0;
v___x_950_ = 1;
v___x_951_ = 1;
v___x_952_ = l_Lean_Meta_mkLambdaFVars(v_fvars_925_, v_a_948_, v___x_949_, v_usedLetOnly_922_, v___x_949_, v___x_950_, v___x_951_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec_ref(v_fvars_925_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_954_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_a_953_);
lean_dec_ref_known(v___x_952_, 1);
v___x_954_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_920_, v_post_921_, v_usedLetOnly_922_, v_skipConstInApp_923_, v_skipInstances_924_, v_a_953_, v_a_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
return v___x_954_;
}
else
{
lean_dec_ref(v_post_921_);
lean_dec_ref(v_pre_920_);
return v___x_952_;
}
}
else
{
lean_dec_ref(v_fvars_925_);
lean_dec_ref(v_post_921_);
lean_dec_ref(v_pre_920_);
return v___x_947_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_920_ = stack[0].m_obj;
lean_object* v_post_921_ = stack[1].m_obj;
uint8_t v_usedLetOnly_922_ = stack[2].m_num;
uint8_t v_skipConstInApp_923_ = stack[3].m_num;
uint8_t v_skipInstances_924_ = stack[4].m_num;
lean_object* v_fvars_925_ = stack[5].m_obj;
lean_object* v_e_926_ = stack[6].m_obj;
lean_object* v_a_927_ = stack[7].m_obj;
lean_object* v___y_928_ = stack[8].m_obj;
lean_object* v___y_929_ = stack[9].m_obj;
lean_object* v___y_930_ = stack[10].m_obj;
lean_object* v___y_931_ = stack[11].m_obj;
lean_object* v_res_955_;
v_res_955_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_920_, v_post_921_, v_usedLetOnly_922_, v_skipConstInApp_923_, v_skipInstances_924_, v_fvars_925_, v_e_926_, v_a_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
stack->m_obj
 = v_res_955_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(lean_object* v_fvars_956_, lean_object* v_pre_957_, lean_object* v_post_958_, uint8_t v_usedLetOnly_959_, uint8_t v_skipConstInApp_960_, uint8_t v_skipInstances_961_, lean_object* v_body_962_, lean_object* v_x_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_array_push(v_fvars_956_, v_x_963_);
v___x_971_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_957_, v_post_958_, v_usedLetOnly_959_, v_skipConstInApp_960_, v_skipInstances_961_, v___x_970_, v_body_962_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
return v___x_971_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_956_ = stack[0].m_obj;
lean_object* v_pre_957_ = stack[1].m_obj;
lean_object* v_post_958_ = stack[2].m_obj;
uint8_t v_usedLetOnly_959_ = stack[3].m_num;
uint8_t v_skipConstInApp_960_ = stack[4].m_num;
uint8_t v_skipInstances_961_ = stack[5].m_num;
lean_object* v_body_962_ = stack[6].m_obj;
lean_object* v_x_963_ = stack[7].m_obj;
lean_object* v___y_964_ = stack[8].m_obj;
lean_object* v___y_965_ = stack[9].m_obj;
lean_object* v___y_966_ = stack[10].m_obj;
lean_object* v___y_967_ = stack[11].m_obj;
lean_object* v___y_968_ = stack[12].m_obj;
lean_object* v_res_972_;
v_res_972_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(v_fvars_956_, v_pre_957_, v_post_958_, v_usedLetOnly_959_, v_skipConstInApp_960_, v_skipInstances_961_, v_body_962_, v_x_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
stack->m_obj
 = v_res_972_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed(lean_object* v_fvars_973_, lean_object* v_pre_974_, lean_object* v_post_975_, lean_object* v_usedLetOnly_976_, lean_object* v_skipConstInApp_977_, lean_object* v_skipInstances_978_, lean_object* v_body_979_, lean_object* v_x_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
uint8_t v_usedLetOnly_boxed_987_; uint8_t v_skipConstInApp_boxed_988_; uint8_t v_skipInstances_boxed_989_; lean_object* v_res_990_; 
v_usedLetOnly_boxed_987_ = lean_unbox(v_usedLetOnly_976_);
v_skipConstInApp_boxed_988_ = lean_unbox(v_skipConstInApp_977_);
v_skipInstances_boxed_989_ = lean_unbox(v_skipInstances_978_);
v_res_990_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(v_fvars_973_, v_pre_974_, v_post_975_, v_usedLetOnly_boxed_987_, v_skipConstInApp_boxed_988_, v_skipInstances_boxed_989_, v_body_979_, v_x_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
return v_res_990_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(lean_object* v_pre_991_, lean_object* v_post_992_, uint8_t v_usedLetOnly_993_, uint8_t v_skipConstInApp_994_, uint8_t v_skipInstances_995_, lean_object* v_fvars_996_, lean_object* v_e_997_, lean_object* v_a_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
if (lean_obj_tag(v_e_997_) == 8)
{
lean_object* v_declName_1004_; lean_object* v_type_1005_; lean_object* v_value_1006_; lean_object* v_body_1007_; uint8_t v_nondep_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___f_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_declName_1004_ = lean_ctor_get(v_e_997_, 0);
lean_inc(v_declName_1004_);
v_type_1005_ = lean_ctor_get(v_e_997_, 1);
lean_inc_ref(v_type_1005_);
v_value_1006_ = lean_ctor_get(v_e_997_, 2);
lean_inc_ref(v_value_1006_);
v_body_1007_ = lean_ctor_get(v_e_997_, 3);
lean_inc_ref(v_body_1007_);
v_nondep_1008_ = lean_ctor_get_uint8(v_e_997_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_997_, 4);
v___x_1009_ = lean_box(v_usedLetOnly_993_);
v___x_1010_ = lean_box(v_skipConstInApp_994_);
v___x_1011_ = lean_box(v_skipInstances_995_);
lean_inc_ref_n(v_post_992_, 2);
lean_inc_ref_n(v_pre_991_, 2);
lean_inc_ref(v_fvars_996_);
v___f_1012_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1012_, 0, v_fvars_996_);
lean_closure_set(v___f_1012_, 1, v_pre_991_);
lean_closure_set(v___f_1012_, 2, v_post_992_);
lean_closure_set(v___f_1012_, 3, v___x_1009_);
lean_closure_set(v___f_1012_, 4, v___x_1010_);
lean_closure_set(v___f_1012_, 5, v___x_1011_);
lean_closure_set(v___f_1012_, 6, v_body_1007_);
v___x_1013_ = lean_expr_instantiate_rev(v_type_1005_, v_fvars_996_);
lean_dec_ref(v_type_1005_);
v___x_1014_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_991_, v_post_992_, v_usedLetOnly_993_, v_skipConstInApp_994_, v_skipInstances_995_, v___x_1013_, v_a_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v___x_1014_, 1);
v___x_1016_ = lean_expr_instantiate_rev(v_value_1006_, v_fvars_996_);
lean_dec_ref(v_fvars_996_);
lean_dec_ref(v_value_1006_);
v___x_1017_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_991_, v_post_992_, v_usedLetOnly_993_, v_skipConstInApp_994_, v_skipInstances_995_, v___x_1016_, v_a_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; uint8_t v___x_1019_; lean_object* v___x_1020_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref_known(v___x_1017_, 1);
v___x_1019_ = 0;
v___x_1020_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_1004_, v_a_1015_, v_a_1018_, v___f_1012_, v_nondep_1008_, v___x_1019_, v_a_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
return v___x_1020_;
}
else
{
lean_dec(v_a_1015_);
lean_dec_ref(v___f_1012_);
lean_dec(v_declName_1004_);
return v___x_1017_;
}
}
else
{
lean_dec_ref(v___f_1012_);
lean_dec_ref(v_value_1006_);
lean_dec(v_declName_1004_);
lean_dec_ref(v_fvars_996_);
lean_dec_ref(v_post_992_);
lean_dec_ref(v_pre_991_);
return v___x_1014_;
}
}
else
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_expr_instantiate_rev(v_e_997_, v_fvars_996_);
lean_dec_ref(v_e_997_);
lean_inc_ref(v_post_992_);
lean_inc_ref(v_pre_991_);
v___x_1022_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_991_, v_post_992_, v_usedLetOnly_993_, v_skipConstInApp_994_, v_skipInstances_995_, v___x_1021_, v_a_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; uint8_t v___x_1024_; uint8_t v___x_1025_; lean_object* v___x_1026_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v___x_1022_, 1);
v___x_1024_ = 0;
v___x_1025_ = 1;
v___x_1026_ = l_Lean_Meta_mkLetFVars(v_fvars_996_, v_a_1023_, v_usedLetOnly_993_, v___x_1024_, v___x_1025_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec_ref(v_fvars_996_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1028_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v___x_1026_, 1);
v___x_1028_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_991_, v_post_992_, v_usedLetOnly_993_, v_skipConstInApp_994_, v_skipInstances_995_, v_a_1027_, v_a_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
return v___x_1028_;
}
else
{
lean_dec_ref(v_post_992_);
lean_dec_ref(v_pre_991_);
return v___x_1026_;
}
}
else
{
lean_dec_ref(v_fvars_996_);
lean_dec_ref(v_post_992_);
lean_dec_ref(v_pre_991_);
return v___x_1022_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_991_ = stack[0].m_obj;
lean_object* v_post_992_ = stack[1].m_obj;
uint8_t v_usedLetOnly_993_ = stack[2].m_num;
uint8_t v_skipConstInApp_994_ = stack[3].m_num;
uint8_t v_skipInstances_995_ = stack[4].m_num;
lean_object* v_fvars_996_ = stack[5].m_obj;
lean_object* v_e_997_ = stack[6].m_obj;
lean_object* v_a_998_ = stack[7].m_obj;
lean_object* v___y_999_ = stack[8].m_obj;
lean_object* v___y_1000_ = stack[9].m_obj;
lean_object* v___y_1001_ = stack[10].m_obj;
lean_object* v___y_1002_ = stack[11].m_obj;
lean_object* v_res_1029_;
v_res_1029_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_991_, v_post_992_, v_usedLetOnly_993_, v_skipConstInApp_994_, v_skipInstances_995_, v_fvars_996_, v_e_997_, v_a_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
stack->m_obj
 = v_res_1029_;
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1030_; lean_object* v_dummy_1031_; 
v___x_1030_ = lean_box(0);
v_dummy_1031_ = l_Lean_Expr_sort___override(v___x_1030_);
return v_dummy_1031_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(lean_object* v_pre_1032_, lean_object* v_post_1033_, uint8_t v_usedLetOnly_1034_, uint8_t v_skipConstInApp_1035_, uint8_t v_skipInstances_1036_, size_t v_sz_1037_, size_t v_i_1038_, lean_object* v_bs_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
uint8_t v___x_1046_; 
v___x_1046_ = lean_usize_dec_lt(v_i_1038_, v_sz_1037_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1047_; 
lean_dec_ref(v_post_1033_);
lean_dec_ref(v_pre_1032_);
v___x_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1047_, 0, v_bs_1039_);
return v___x_1047_;
}
else
{
lean_object* v_v_1048_; lean_object* v___x_1049_; lean_object* v_bs_x27_1050_; lean_object* v___x_1051_; 
v_v_1048_ = lean_array_uget(v_bs_1039_, v_i_1038_);
v___x_1049_ = lean_unsigned_to_nat(0u);
v_bs_x27_1050_ = lean_array_uset(v_bs_1039_, v_i_1038_, v___x_1049_);
lean_inc_ref(v_post_1033_);
lean_inc_ref(v_pre_1032_);
v___x_1051_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1032_, v_post_1033_, v_usedLetOnly_1034_, v_skipConstInApp_1035_, v_skipInstances_1036_, v_v_1048_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; size_t v___x_1053_; size_t v___x_1054_; lean_object* v___x_1055_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1052_);
lean_dec_ref_known(v___x_1051_, 1);
v___x_1053_ = ((size_t)1ULL);
v___x_1054_ = lean_usize_add(v_i_1038_, v___x_1053_);
v___x_1055_ = lean_array_uset(v_bs_x27_1050_, v_i_1038_, v_a_1052_);
v_i_1038_ = v___x_1054_;
v_bs_1039_ = v___x_1055_;
goto _start;
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec_ref(v_bs_x27_1050_);
lean_dec_ref(v_post_1033_);
lean_dec_ref(v_pre_1032_);
v_a_1057_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1051_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1051_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1032_ = stack[0].m_obj;
lean_object* v_post_1033_ = stack[1].m_obj;
uint8_t v_usedLetOnly_1034_ = stack[2].m_num;
uint8_t v_skipConstInApp_1035_ = stack[3].m_num;
uint8_t v_skipInstances_1036_ = stack[4].m_num;
size_t v_sz_1037_ = stack[5].m_num;
size_t v_i_1038_ = stack[6].m_num;
lean_object* v_bs_1039_ = stack[7].m_obj;
lean_object* v___y_1040_ = stack[8].m_obj;
lean_object* v___y_1041_ = stack[9].m_obj;
lean_object* v___y_1042_ = stack[10].m_obj;
lean_object* v___y_1043_ = stack[11].m_obj;
lean_object* v___y_1044_ = stack[12].m_obj;
lean_object* v_res_1065_;
v_res_1065_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_pre_1032_, v_post_1033_, v_usedLetOnly_1034_, v_skipConstInApp_1035_, v_skipInstances_1036_, v_sz_1037_, v_i_1038_, v_bs_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
stack->m_obj
 = v_res_1065_;
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_pre_1066_, lean_object* v_post_1067_, uint8_t v_usedLetOnly_1068_, uint8_t v_skipConstInApp_1069_, uint8_t v_skipInstances_1070_, lean_object* v___x_1071_, lean_object* v___y_1072_, lean_object* v_b_1073_, lean_object* v_a_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1066_, v_post_1067_, v_usedLetOnly_1068_, v_skipConstInApp_1069_, v_skipInstances_1070_, v___x_1071_, v___y_1072_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1090_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1090_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1090_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1085_ = lean_array_fset(v_b_1073_, v_a_1074_, v_a_1081_);
v___x_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1086_);
v___x_1088_ = v___x_1083_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec_ref(v_b_1073_);
v_a_1091_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1080_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1080_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
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
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1066_ = stack[0].m_obj;
lean_object* v_post_1067_ = stack[1].m_obj;
uint8_t v_usedLetOnly_1068_ = stack[2].m_num;
uint8_t v_skipConstInApp_1069_ = stack[3].m_num;
uint8_t v_skipInstances_1070_ = stack[4].m_num;
lean_object* v___x_1071_ = stack[5].m_obj;
lean_object* v___y_1072_ = stack[6].m_obj;
lean_object* v_b_1073_ = stack[7].m_obj;
lean_object* v_a_1074_ = stack[8].m_obj;
lean_object* v___y_1075_ = stack[9].m_obj;
lean_object* v___y_1076_ = stack[10].m_obj;
lean_object* v___y_1077_ = stack[11].m_obj;
lean_object* v___y_1078_ = stack[12].m_obj;
lean_object* v_res_1099_;
v_res_1099_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_1066_, v_post_1067_, v_usedLetOnly_1068_, v_skipConstInApp_1069_, v_skipInstances_1070_, v___x_1071_, v___y_1072_, v_b_1073_, v_a_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
stack->m_obj
 = v_res_1099_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_pre_1100_, lean_object* v_post_1101_, lean_object* v_usedLetOnly_1102_, lean_object* v_skipConstInApp_1103_, lean_object* v_skipInstances_1104_, lean_object* v___x_1105_, lean_object* v___y_1106_, lean_object* v_b_1107_, lean_object* v_a_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
uint8_t v_usedLetOnly_boxed_1114_; uint8_t v_skipConstInApp_boxed_1115_; uint8_t v_skipInstances_boxed_1116_; lean_object* v_res_1117_; 
v_usedLetOnly_boxed_1114_ = lean_unbox(v_usedLetOnly_1102_);
v_skipConstInApp_boxed_1115_ = lean_unbox(v_skipConstInApp_1103_);
v_skipInstances_boxed_1116_ = lean_unbox(v_skipInstances_1104_);
v_res_1117_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_1100_, v_post_1101_, v_usedLetOnly_boxed_1114_, v_skipConstInApp_boxed_1115_, v_skipInstances_boxed_1116_, v___x_1105_, v___y_1106_, v_b_1107_, v_a_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v_a_1108_);
lean_dec(v___y_1106_);
return v_res_1117_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(lean_object* v_upperBound_1118_, lean_object* v___x_1119_, lean_object* v_pre_1120_, lean_object* v_post_1121_, uint8_t v_usedLetOnly_1122_, uint8_t v_skipConstInApp_1123_, uint8_t v_skipInstances_1124_, lean_object* v_a_1125_, lean_object* v_b_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v___y_1134_; uint8_t v___x_1157_; 
v___x_1157_ = lean_nat_dec_lt(v_a_1125_, v_upperBound_1118_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; 
lean_dec(v_a_1125_);
lean_dec_ref(v_post_1121_);
lean_dec_ref(v_pre_1120_);
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v_b_1126_);
return v___x_1158_;
}
else
{
lean_object* v___x_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; 
v___x_1159_ = lean_array_fget_borrowed(v_b_1126_, v_a_1125_);
v___x_1160_ = lean_array_get_size(v___x_1119_);
v___x_1161_ = lean_nat_dec_lt(v_a_1125_, v___x_1160_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___f_1165_; 
lean_inc(v___x_1159_);
v___x_1162_ = lean_box(v_usedLetOnly_1122_);
v___x_1163_ = lean_box(v_skipConstInApp_1123_);
v___x_1164_ = lean_box(v_skipInstances_1124_);
lean_inc(v_a_1125_);
lean_inc(v___y_1127_);
lean_inc_ref(v_post_1121_);
lean_inc_ref(v_pre_1120_);
v___f_1165_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1165_, 0, v_pre_1120_);
lean_closure_set(v___f_1165_, 1, v_post_1121_);
lean_closure_set(v___f_1165_, 2, v___x_1162_);
lean_closure_set(v___f_1165_, 3, v___x_1163_);
lean_closure_set(v___f_1165_, 4, v___x_1164_);
lean_closure_set(v___f_1165_, 5, v___x_1159_);
lean_closure_set(v___f_1165_, 6, v___y_1127_);
lean_closure_set(v___f_1165_, 7, v_b_1126_);
lean_closure_set(v___f_1165_, 8, v_a_1125_);
v___y_1134_ = v___f_1165_;
goto v___jp_1133_;
}
else
{
lean_object* v___x_1166_; uint8_t v_isInstance_1167_; 
v___x_1166_ = lean_array_fget_borrowed(v___x_1119_, v_a_1125_);
v_isInstance_1167_ = lean_ctor_get_uint8(v___x_1166_, sizeof(void*)*1 + 4);
if (v_isInstance_1167_ == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___f_1171_; 
lean_inc(v___x_1159_);
v___x_1168_ = lean_box(v_usedLetOnly_1122_);
v___x_1169_ = lean_box(v_skipConstInApp_1123_);
v___x_1170_ = lean_box(v_skipInstances_1124_);
lean_inc(v_a_1125_);
lean_inc(v___y_1127_);
lean_inc_ref(v_post_1121_);
lean_inc_ref(v_pre_1120_);
v___f_1171_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1171_, 0, v_pre_1120_);
lean_closure_set(v___f_1171_, 1, v_post_1121_);
lean_closure_set(v___f_1171_, 2, v___x_1168_);
lean_closure_set(v___f_1171_, 3, v___x_1169_);
lean_closure_set(v___f_1171_, 4, v___x_1170_);
lean_closure_set(v___f_1171_, 5, v___x_1159_);
lean_closure_set(v___f_1171_, 6, v___y_1127_);
lean_closure_set(v___f_1171_, 7, v_b_1126_);
lean_closure_set(v___f_1171_, 8, v_a_1125_);
v___y_1134_ = v___f_1171_;
goto v___jp_1133_;
}
else
{
lean_object* v___x_1172_; lean_object* v___f_1173_; 
v___x_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1172_, 0, v_b_1126_);
v___f_1173_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1173_, 0, v___x_1172_);
v___y_1134_ = v___f_1173_;
goto v___jp_1133_;
}
}
}
v___jp_1133_:
{
lean_object* v___x_1135_; 
lean_inc(v___y_1131_);
lean_inc_ref(v___y_1130_);
lean_inc(v___y_1129_);
lean_inc_ref(v___y_1128_);
v___x_1135_ = lean_apply_5(v___y_1134_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, lean_box(0));
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1148_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1138_ = v___x_1135_;
v_isShared_1139_ = v_isSharedCheck_1148_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1135_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1148_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
if (lean_obj_tag(v_a_1136_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1142_; 
lean_dec(v_a_1125_);
lean_dec_ref(v_post_1121_);
lean_dec_ref(v_pre_1120_);
v_a_1140_ = lean_ctor_get(v_a_1136_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v_a_1136_, 1);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v_a_1140_);
v___x_1142_ = v___x_1138_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1140_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_del_object(v___x_1138_);
v_a_1144_ = lean_ctor_get(v_a_1136_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v_a_1136_, 1);
v___x_1145_ = lean_unsigned_to_nat(1u);
v___x_1146_ = lean_nat_add(v_a_1125_, v___x_1145_);
lean_dec(v_a_1125_);
v_a_1125_ = v___x_1146_;
v_b_1126_ = v_a_1144_;
goto _start;
}
}
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_dec(v_a_1125_);
lean_dec_ref(v_post_1121_);
lean_dec_ref(v_pre_1120_);
v_a_1149_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1135_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1135_);
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
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1118_ = stack[0].m_obj;
lean_object* v___x_1119_ = stack[1].m_obj;
lean_object* v_pre_1120_ = stack[2].m_obj;
lean_object* v_post_1121_ = stack[3].m_obj;
uint8_t v_usedLetOnly_1122_ = stack[4].m_num;
uint8_t v_skipConstInApp_1123_ = stack[5].m_num;
uint8_t v_skipInstances_1124_ = stack[6].m_num;
lean_object* v_a_1125_ = stack[7].m_obj;
lean_object* v_b_1126_ = stack[8].m_obj;
lean_object* v___y_1127_ = stack[9].m_obj;
lean_object* v___y_1128_ = stack[10].m_obj;
lean_object* v___y_1129_ = stack[11].m_obj;
lean_object* v___y_1130_ = stack[12].m_obj;
lean_object* v___y_1131_ = stack[13].m_obj;
lean_object* v_res_1174_;
v_res_1174_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v_upperBound_1118_, v___x_1119_, v_pre_1120_, v_post_1121_, v_usedLetOnly_1122_, v_skipConstInApp_1123_, v_skipInstances_1124_, v_a_1125_, v_b_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
stack->m_obj
 = v_res_1174_;
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(uint8_t v_skipInstances_1175_, lean_object* v_pre_1176_, lean_object* v_post_1177_, uint8_t v_usedLetOnly_1178_, uint8_t v_skipConstInApp_1179_, lean_object* v_x_1180_, lean_object* v_x_1181_, lean_object* v_x_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_f_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; 
if (lean_obj_tag(v_x_1180_) == 5)
{
lean_object* v_fn_1238_; lean_object* v_arg_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v_fn_1238_ = lean_ctor_get(v_x_1180_, 0);
lean_inc_ref(v_fn_1238_);
v_arg_1239_ = lean_ctor_get(v_x_1180_, 1);
lean_inc_ref(v_arg_1239_);
lean_dec_ref_known(v_x_1180_, 2);
v___x_1240_ = lean_array_set(v_x_1181_, v_x_1182_, v_arg_1239_);
v___x_1241_ = lean_unsigned_to_nat(1u);
v___x_1242_ = lean_nat_sub(v_x_1182_, v___x_1241_);
lean_dec(v_x_1182_);
v_x_1180_ = v_fn_1238_;
v_x_1181_ = v___x_1240_;
v_x_1182_ = v___x_1242_;
goto _start;
}
else
{
lean_dec(v_x_1182_);
if (v_skipConstInApp_1179_ == 0)
{
goto v___jp_1235_;
}
else
{
uint8_t v___x_1244_; 
v___x_1244_ = l_Lean_Expr_isConst(v_x_1180_);
if (v___x_1244_ == 0)
{
goto v___jp_1235_;
}
else
{
v_f_1190_ = v_x_1180_;
v___y_1191_ = v___y_1183_;
v___y_1192_ = v___y_1184_;
v___y_1193_ = v___y_1185_;
v___y_1194_ = v___y_1186_;
v___y_1195_ = v___y_1187_;
goto v___jp_1189_;
}
}
}
v___jp_1189_:
{
if (v_skipInstances_1175_ == 0)
{
size_t v_sz_1196_; size_t v___x_1197_; lean_object* v___x_1198_; 
v_sz_1196_ = lean_array_size(v_x_1181_);
v___x_1197_ = ((size_t)0ULL);
lean_inc_ref(v_post_1177_);
lean_inc_ref(v_pre_1176_);
v___x_1198_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_pre_1176_, v_post_1177_, v_usedLetOnly_1178_, v_skipConstInApp_1179_, v_skipInstances_1175_, v_sz_1196_, v___x_1197_, v_x_1181_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref_known(v___x_1198_, 1);
v___x_1200_ = l_Lean_mkAppN(v_f_1190_, v_a_1199_);
lean_dec(v_a_1199_);
v___x_1201_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1176_, v_post_1177_, v_usedLetOnly_1178_, v_skipConstInApp_1179_, v_skipInstances_1175_, v___x_1200_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
return v___x_1201_;
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec_ref(v_f_1190_);
lean_dec_ref(v_post_1177_);
lean_dec_ref(v_pre_1176_);
v_a_1202_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1198_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1198_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
else
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_array_get_size(v_x_1181_);
lean_inc_ref(v_f_1190_);
v___x_1211_ = l_Lean_Meta_getFunInfoNArgs(v_f_1190_, v___x_1210_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v_paramInfo_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1212_);
lean_dec_ref_known(v___x_1211_, 1);
v_paramInfo_1213_ = lean_ctor_get(v_a_1212_, 0);
lean_inc_ref(v_paramInfo_1213_);
lean_dec(v_a_1212_);
v___x_1214_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1177_);
lean_inc_ref(v_pre_1176_);
v___x_1215_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v___x_1210_, v_paramInfo_1213_, v_pre_1176_, v_post_1177_, v_usedLetOnly_1178_, v_skipConstInApp_1179_, v_skipInstances_1175_, v___x_1214_, v_x_1181_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
lean_dec_ref(v_paramInfo_1213_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v___x_1215_, 1);
v___x_1217_ = l_Lean_mkAppN(v_f_1190_, v_a_1216_);
lean_dec(v_a_1216_);
v___x_1218_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1176_, v_post_1177_, v_usedLetOnly_1178_, v_skipConstInApp_1179_, v_skipInstances_1175_, v___x_1217_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
return v___x_1218_;
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_dec_ref(v_f_1190_);
lean_dec_ref(v_post_1177_);
lean_dec_ref(v_pre_1176_);
v_a_1219_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1215_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1215_);
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
lean_dec_ref(v_f_1190_);
lean_dec_ref(v_x_1181_);
lean_dec_ref(v_post_1177_);
lean_dec_ref(v_pre_1176_);
v_a_1227_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1211_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1211_);
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
lean_inc_ref(v_post_1177_);
lean_inc_ref(v_pre_1176_);
v___x_1236_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1176_, v_post_1177_, v_usedLetOnly_1178_, v_skipConstInApp_1179_, v_skipInstances_1175_, v_x_1180_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1237_);
lean_dec_ref_known(v___x_1236_, 1);
v_f_1190_ = v_a_1237_;
v___y_1191_ = v___y_1183_;
v___y_1192_ = v___y_1184_;
v___y_1193_ = v___y_1185_;
v___y_1194_ = v___y_1186_;
v___y_1195_ = v___y_1187_;
goto v___jp_1189_;
}
else
{
lean_dec_ref(v_x_1181_);
lean_dec_ref(v_post_1177_);
lean_dec_ref(v_pre_1176_);
return v___x_1236_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8_0interp(lean_interpreter_value* stack)
{
uint8_t v_skipInstances_1175_ = stack[0].m_num;
lean_object* v_pre_1176_ = stack[1].m_obj;
lean_object* v_post_1177_ = stack[2].m_obj;
uint8_t v_usedLetOnly_1178_ = stack[3].m_num;
uint8_t v_skipConstInApp_1179_ = stack[4].m_num;
lean_object* v_x_1180_ = stack[5].m_obj;
lean_object* v_x_1181_ = stack[6].m_obj;
lean_object* v_x_1182_ = stack[7].m_obj;
lean_object* v___y_1183_ = stack[8].m_obj;
lean_object* v___y_1184_ = stack[9].m_obj;
lean_object* v___y_1185_ = stack[10].m_obj;
lean_object* v___y_1186_ = stack[11].m_obj;
lean_object* v___y_1187_ = stack[12].m_obj;
lean_object* v_res_1245_;
v_res_1245_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_1175_, v_pre_1176_, v_post_1177_, v_usedLetOnly_1178_, v_skipConstInApp_1179_, v_x_1180_, v_x_1181_, v_x_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
stack->m_obj
 = v_res_1245_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(lean_object* v___x_1246_, lean_object* v_pre_1247_, lean_object* v_e_1248_, lean_object* v_post_1249_, uint8_t v_usedLetOnly_1250_, uint8_t v_skipConstInApp_1251_, uint8_t v_skipInstances_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_Core_checkSystem(v___x_1246_, v___y_1256_, v___y_1257_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v___x_1260_; 
lean_dec_ref_known(v___x_1259_, 1);
lean_inc_ref(v_pre_1247_);
lean_inc(v___y_1257_);
lean_inc_ref(v___y_1256_);
lean_inc(v___y_1255_);
lean_inc_ref(v___y_1254_);
lean_inc_ref(v_e_1248_);
v___x_1260_ = lean_apply_6(v_pre_1247_, v_e_1248_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, lean_box(0));
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
lean_dec_ref(v_post_1249_);
lean_dec_ref(v_e_1248_);
lean_dec_ref(v_pre_1247_);
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
lean_dec_ref(v_e_1248_);
v_e_1305_ = lean_ctor_get(v_a_1261_, 0);
lean_inc_ref(v_e_1305_);
lean_dec_ref_known(v_a_1261_, 1);
v___x_1306_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1247_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v_skipInstances_1252_, v_e_1305_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
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
v___y_1266_ = v_e_1248_;
goto v___jp_1265_;
}
else
{
lean_object* v_val_1308_; 
lean_dec_ref(v_e_1248_);
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
v___x_1268_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1247_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v_skipInstances_1252_, v___x_1267_, v___y_1266_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v___x_1268_;
}
case 6:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1270_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_1247_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v_skipInstances_1252_, v___x_1269_, v___y_1266_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v___x_1270_;
}
case 8:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1272_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_1247_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v_skipInstances_1252_, v___x_1271_, v___y_1266_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
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
v___x_1278_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_1252_, v_pre_1247_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v___y_1266_, v___x_1275_, v___x_1277_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v___x_1278_;
}
case 10:
{
lean_object* v_data_1279_; lean_object* v_expr_1280_; lean_object* v___x_1281_; 
v_data_1279_ = lean_ctor_get(v___y_1266_, 0);
v_expr_1280_ = lean_ctor_get(v___y_1266_, 1);
lean_inc_ref(v_expr_1280_);
lean_inc_ref(v_post_1249_);
lean_inc_ref(v_pre_1247_);
v___x_1281_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1247_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v_skipInstances_1252_, v_expr_1280_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
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
v___x_1287_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1247_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v_skipInstances_1252_, v___x_1286_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v___x_1287_;
}
else
{
lean_object* v___x_1288_; 
lean_dec(v_a_1282_);
v___x_1288_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1247_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v_skipInstances_1252_, v___y_1266_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v___x_1288_;
}
}
else
{
lean_dec_ref_known(v___y_1266_, 2);
lean_dec_ref(v_post_1249_);
lean_dec_ref(v_pre_1247_);
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
lean_inc_ref(v_post_1249_);
lean_inc_ref(v_pre_1247_);
v___x_1292_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1247_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v_skipInstances_1252_, v_struct_1291_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
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
v___x_1298_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1247_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v_skipInstances_1252_, v___x_1297_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v___x_1298_;
}
else
{
lean_object* v___x_1299_; 
lean_dec(v_a_1293_);
v___x_1299_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1247_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v_skipInstances_1252_, v___y_1266_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v___x_1299_;
}
}
else
{
lean_dec_ref_known(v___y_1266_, 3);
lean_dec_ref(v_post_1249_);
lean_dec_ref(v_pre_1247_);
return v___x_1292_;
}
}
default: 
{
lean_object* v___x_1300_; 
v___x_1300_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1247_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v_skipInstances_1252_, v___y_1266_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v___x_1300_;
}
}
}
}
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
lean_dec_ref(v_post_1249_);
lean_dec_ref(v_e_1248_);
lean_dec_ref(v_pre_1247_);
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
lean_dec_ref(v_post_1249_);
lean_dec_ref(v_e_1248_);
lean_dec_ref(v_pre_1247_);
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
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1246_ = stack[0].m_obj;
lean_object* v_pre_1247_ = stack[1].m_obj;
lean_object* v_e_1248_ = stack[2].m_obj;
lean_object* v_post_1249_ = stack[3].m_obj;
uint8_t v_usedLetOnly_1250_ = stack[4].m_num;
uint8_t v_skipConstInApp_1251_ = stack[5].m_num;
uint8_t v_skipInstances_1252_ = stack[6].m_num;
lean_object* v___y_1253_ = stack[7].m_obj;
lean_object* v___y_1254_ = stack[8].m_obj;
lean_object* v___y_1255_ = stack[9].m_obj;
lean_object* v___y_1256_ = stack[10].m_obj;
lean_object* v___y_1257_ = stack[11].m_obj;
lean_object* v_res_1326_;
v_res_1326_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(v___x_1246_, v_pre_1247_, v_e_1248_, v_post_1249_, v_usedLetOnly_1250_, v_skipConstInApp_1251_, v_skipInstances_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
stack->m_obj
 = v_res_1326_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1327_, lean_object* v_pre_1328_, lean_object* v_e_1329_, lean_object* v_post_1330_, lean_object* v_usedLetOnly_1331_, lean_object* v_skipConstInApp_1332_, lean_object* v_skipInstances_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
uint8_t v_usedLetOnly_boxed_1340_; uint8_t v_skipConstInApp_boxed_1341_; uint8_t v_skipInstances_boxed_1342_; lean_object* v_res_1343_; 
v_usedLetOnly_boxed_1340_ = lean_unbox(v_usedLetOnly_1331_);
v_skipConstInApp_boxed_1341_ = lean_unbox(v_skipConstInApp_1332_);
v_skipInstances_boxed_1342_ = lean_unbox(v_skipInstances_1333_);
v_res_1343_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(v___x_1327_, v_pre_1328_, v_e_1329_, v_post_1330_, v_usedLetOnly_boxed_1340_, v_skipConstInApp_boxed_1341_, v_skipInstances_boxed_1342_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
return v_res_1343_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(lean_object* v_pre_1344_, lean_object* v_post_1345_, uint8_t v_usedLetOnly_1346_, uint8_t v_skipConstInApp_1347_, uint8_t v_skipInstances_1348_, lean_object* v_e_1349_, lean_object* v_a_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_inc(v_a_1350_);
v___x_1356_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1356_, 0, lean_box(0));
lean_closure_set(v___x_1356_, 1, lean_box(0));
lean_closure_set(v___x_1356_, 2, v_a_1350_);
v___x_1357_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v___x_1356_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1392_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1392_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1392_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1362_; 
v___x_1362_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_a_1358_, v_e_1349_);
lean_dec(v_a_1358_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___f_1367_; lean_object* v___x_1368_; 
lean_del_object(v___x_1360_);
v___x_1363_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0));
v___x_1364_ = lean_box(v_usedLetOnly_1346_);
v___x_1365_ = lean_box(v_skipConstInApp_1347_);
v___x_1366_ = lean_box(v_skipInstances_1348_);
lean_inc_ref(v_e_1349_);
v___f_1367_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed), 13, 7);
lean_closure_set(v___f_1367_, 0, v___x_1363_);
lean_closure_set(v___f_1367_, 1, v_pre_1344_);
lean_closure_set(v___f_1367_, 2, v_e_1349_);
lean_closure_set(v___f_1367_, 3, v_post_1345_);
lean_closure_set(v___f_1367_, 4, v___x_1364_);
lean_closure_set(v___f_1367_, 5, v___x_1365_);
lean_closure_set(v___f_1367_, 6, v___x_1366_);
v___x_1368_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v___f_1367_, v_a_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___f_1370_; lean_object* v___x_1371_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc_n(v_a_1369_, 2);
lean_dec_ref_known(v___x_1368_, 1);
lean_inc(v_a_1350_);
v___f_1370_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1370_, 0, v_a_1350_);
lean_closure_set(v___f_1370_, 1, v_e_1349_);
lean_closure_set(v___f_1370_, 2, v_a_1369_);
v___x_1371_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v___f_1370_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1378_ == 0)
{
lean_object* v_unused_1379_; 
v_unused_1379_ = lean_ctor_get(v___x_1371_, 0);
lean_dec(v_unused_1379_);
v___x_1373_ = v___x_1371_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_dec(v___x_1371_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v_a_1369_);
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1369_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_dec(v_a_1369_);
v_a_1380_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1371_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1371_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
else
{
lean_dec_ref(v_e_1349_);
return v___x_1368_;
}
}
else
{
lean_object* v_val_1388_; lean_object* v___x_1390_; 
lean_dec_ref(v_e_1349_);
lean_dec_ref(v_post_1345_);
lean_dec_ref(v_pre_1344_);
v_val_1388_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_val_1388_);
lean_dec_ref_known(v___x_1362_, 1);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v_val_1388_);
v___x_1390_ = v___x_1360_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_val_1388_);
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
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_dec_ref(v_e_1349_);
lean_dec_ref(v_post_1345_);
lean_dec_ref(v_pre_1344_);
v_a_1393_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1357_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1357_);
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
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1344_ = stack[0].m_obj;
lean_object* v_post_1345_ = stack[1].m_obj;
uint8_t v_usedLetOnly_1346_ = stack[2].m_num;
uint8_t v_skipConstInApp_1347_ = stack[3].m_num;
uint8_t v_skipInstances_1348_ = stack[4].m_num;
lean_object* v_e_1349_ = stack[5].m_obj;
lean_object* v_a_1350_ = stack[6].m_obj;
lean_object* v___y_1351_ = stack[7].m_obj;
lean_object* v___y_1352_ = stack[8].m_obj;
lean_object* v___y_1353_ = stack[9].m_obj;
lean_object* v___y_1354_ = stack[10].m_obj;
lean_object* v_res_1401_;
v_res_1401_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1344_, v_post_1345_, v_usedLetOnly_1346_, v_skipConstInApp_1347_, v_skipInstances_1348_, v_e_1349_, v_a_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
stack->m_obj
 = v_res_1401_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(lean_object* v_pre_1402_, lean_object* v_post_1403_, uint8_t v_usedLetOnly_1404_, uint8_t v_skipConstInApp_1405_, uint8_t v_skipInstances_1406_, lean_object* v_fvars_1407_, lean_object* v_e_1408_, lean_object* v_a_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
if (lean_obj_tag(v_e_1408_) == 7)
{
lean_object* v_binderName_1415_; lean_object* v_binderType_1416_; lean_object* v_body_1417_; uint8_t v_binderInfo_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___f_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v_binderName_1415_ = lean_ctor_get(v_e_1408_, 0);
lean_inc(v_binderName_1415_);
v_binderType_1416_ = lean_ctor_get(v_e_1408_, 1);
lean_inc_ref(v_binderType_1416_);
v_body_1417_ = lean_ctor_get(v_e_1408_, 2);
lean_inc_ref(v_body_1417_);
v_binderInfo_1418_ = lean_ctor_get_uint8(v_e_1408_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1408_, 3);
v___x_1419_ = lean_box(v_usedLetOnly_1404_);
v___x_1420_ = lean_box(v_skipConstInApp_1405_);
v___x_1421_ = lean_box(v_skipInstances_1406_);
lean_inc_ref(v_post_1403_);
lean_inc_ref(v_pre_1402_);
lean_inc_ref(v_fvars_1407_);
v___f_1422_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1422_, 0, v_fvars_1407_);
lean_closure_set(v___f_1422_, 1, v_pre_1402_);
lean_closure_set(v___f_1422_, 2, v_post_1403_);
lean_closure_set(v___f_1422_, 3, v___x_1419_);
lean_closure_set(v___f_1422_, 4, v___x_1420_);
lean_closure_set(v___f_1422_, 5, v___x_1421_);
lean_closure_set(v___f_1422_, 6, v_body_1417_);
v___x_1423_ = lean_expr_instantiate_rev(v_binderType_1416_, v_fvars_1407_);
lean_dec_ref(v_fvars_1407_);
lean_dec_ref(v_binderType_1416_);
v___x_1424_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1402_, v_post_1403_, v_usedLetOnly_1404_, v_skipConstInApp_1405_, v_skipInstances_1406_, v___x_1423_, v_a_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; uint8_t v___x_1426_; lean_object* v___x_1427_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref_known(v___x_1424_, 1);
v___x_1426_ = 0;
v___x_1427_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_1415_, v_binderInfo_1418_, v_a_1425_, v___f_1422_, v___x_1426_, v_a_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
return v___x_1427_;
}
else
{
lean_dec_ref(v___f_1422_);
lean_dec(v_binderName_1415_);
return v___x_1424_;
}
}
else
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = lean_expr_instantiate_rev(v_e_1408_, v_fvars_1407_);
lean_dec_ref(v_e_1408_);
lean_inc_ref(v_post_1403_);
lean_inc_ref(v_pre_1402_);
v___x_1429_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1402_, v_post_1403_, v_usedLetOnly_1404_, v_skipConstInApp_1405_, v_skipInstances_1406_, v___x_1428_, v_a_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; uint8_t v___x_1431_; uint8_t v___x_1432_; uint8_t v___x_1433_; lean_object* v___x_1434_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref_known(v___x_1429_, 1);
v___x_1431_ = 0;
v___x_1432_ = 1;
v___x_1433_ = 1;
v___x_1434_ = l_Lean_Meta_mkForallFVars(v_fvars_1407_, v_a_1430_, v___x_1431_, v_usedLetOnly_1404_, v___x_1432_, v___x_1433_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
lean_dec_ref(v_fvars_1407_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v___x_1436_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
lean_dec_ref_known(v___x_1434_, 1);
v___x_1436_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1402_, v_post_1403_, v_usedLetOnly_1404_, v_skipConstInApp_1405_, v_skipInstances_1406_, v_a_1435_, v_a_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
return v___x_1436_;
}
else
{
lean_dec_ref(v_post_1403_);
lean_dec_ref(v_pre_1402_);
return v___x_1434_;
}
}
else
{
lean_dec_ref(v_fvars_1407_);
lean_dec_ref(v_post_1403_);
lean_dec_ref(v_pre_1402_);
return v___x_1429_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1402_ = stack[0].m_obj;
lean_object* v_post_1403_ = stack[1].m_obj;
uint8_t v_usedLetOnly_1404_ = stack[2].m_num;
uint8_t v_skipConstInApp_1405_ = stack[3].m_num;
uint8_t v_skipInstances_1406_ = stack[4].m_num;
lean_object* v_fvars_1407_ = stack[5].m_obj;
lean_object* v_e_1408_ = stack[6].m_obj;
lean_object* v_a_1409_ = stack[7].m_obj;
lean_object* v___y_1410_ = stack[8].m_obj;
lean_object* v___y_1411_ = stack[9].m_obj;
lean_object* v___y_1412_ = stack[10].m_obj;
lean_object* v___y_1413_ = stack[11].m_obj;
lean_object* v_res_1437_;
v_res_1437_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1402_, v_post_1403_, v_usedLetOnly_1404_, v_skipConstInApp_1405_, v_skipInstances_1406_, v_fvars_1407_, v_e_1408_, v_a_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
stack->m_obj
 = v_res_1437_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(lean_object* v_fvars_1438_, lean_object* v_pre_1439_, lean_object* v_post_1440_, uint8_t v_usedLetOnly_1441_, uint8_t v_skipConstInApp_1442_, uint8_t v_skipInstances_1443_, lean_object* v_body_1444_, lean_object* v_x_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_array_push(v_fvars_1438_, v_x_1445_);
v___x_1453_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1439_, v_post_1440_, v_usedLetOnly_1441_, v_skipConstInApp_1442_, v_skipInstances_1443_, v___x_1452_, v_body_1444_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
return v___x_1453_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_1438_ = stack[0].m_obj;
lean_object* v_pre_1439_ = stack[1].m_obj;
lean_object* v_post_1440_ = stack[2].m_obj;
uint8_t v_usedLetOnly_1441_ = stack[3].m_num;
uint8_t v_skipConstInApp_1442_ = stack[4].m_num;
uint8_t v_skipInstances_1443_ = stack[5].m_num;
lean_object* v_body_1444_ = stack[6].m_obj;
lean_object* v_x_1445_ = stack[7].m_obj;
lean_object* v___y_1446_ = stack[8].m_obj;
lean_object* v___y_1447_ = stack[9].m_obj;
lean_object* v___y_1448_ = stack[10].m_obj;
lean_object* v___y_1449_ = stack[11].m_obj;
lean_object* v___y_1450_ = stack[12].m_obj;
lean_object* v_res_1454_;
v_res_1454_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(v_fvars_1438_, v_pre_1439_, v_post_1440_, v_usedLetOnly_1441_, v_skipConstInApp_1442_, v_skipInstances_1443_, v_body_1444_, v_x_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
stack->m_obj
 = v_res_1454_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1455_, lean_object* v_post_1456_, lean_object* v_usedLetOnly_1457_, lean_object* v_skipConstInApp_1458_, lean_object* v_skipInstances_1459_, lean_object* v_e_1460_, lean_object* v_a_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
uint8_t v_usedLetOnly_boxed_1467_; uint8_t v_skipConstInApp_boxed_1468_; uint8_t v_skipInstances_boxed_1469_; lean_object* v_res_1470_; 
v_usedLetOnly_boxed_1467_ = lean_unbox(v_usedLetOnly_1457_);
v_skipConstInApp_boxed_1468_ = lean_unbox(v_skipConstInApp_1458_);
v_skipInstances_boxed_1469_ = lean_unbox(v_skipInstances_1459_);
v_res_1470_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1455_, v_post_1456_, v_usedLetOnly_boxed_1467_, v_skipConstInApp_boxed_1468_, v_skipInstances_boxed_1469_, v_e_1460_, v_a_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v_a_1461_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1471_, lean_object* v_post_1472_, lean_object* v_usedLetOnly_1473_, lean_object* v_skipConstInApp_1474_, lean_object* v_skipInstances_1475_, lean_object* v_sz_1476_, lean_object* v_i_1477_, lean_object* v_bs_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
uint8_t v_usedLetOnly_boxed_1485_; uint8_t v_skipConstInApp_boxed_1486_; uint8_t v_skipInstances_boxed_1487_; size_t v_sz_boxed_1488_; size_t v_i_boxed_1489_; lean_object* v_res_1490_; 
v_usedLetOnly_boxed_1485_ = lean_unbox(v_usedLetOnly_1473_);
v_skipConstInApp_boxed_1486_ = lean_unbox(v_skipConstInApp_1474_);
v_skipInstances_boxed_1487_ = lean_unbox(v_skipInstances_1475_);
v_sz_boxed_1488_ = lean_unbox_usize(v_sz_1476_);
lean_dec(v_sz_1476_);
v_i_boxed_1489_ = lean_unbox_usize(v_i_1477_);
lean_dec(v_i_1477_);
v_res_1490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_pre_1471_, v_post_1472_, v_usedLetOnly_boxed_1485_, v_skipConstInApp_boxed_1486_, v_skipInstances_boxed_1487_, v_sz_boxed_1488_, v_i_boxed_1489_, v_bs_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___boxed(lean_object* v_pre_1491_, lean_object* v_post_1492_, lean_object* v_usedLetOnly_1493_, lean_object* v_skipConstInApp_1494_, lean_object* v_skipInstances_1495_, lean_object* v_e_1496_, lean_object* v_a_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
uint8_t v_usedLetOnly_boxed_1503_; uint8_t v_skipConstInApp_boxed_1504_; uint8_t v_skipInstances_boxed_1505_; lean_object* v_res_1506_; 
v_usedLetOnly_boxed_1503_ = lean_unbox(v_usedLetOnly_1493_);
v_skipConstInApp_boxed_1504_ = lean_unbox(v_skipConstInApp_1494_);
v_skipInstances_boxed_1505_ = lean_unbox(v_skipInstances_1495_);
v_res_1506_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1491_, v_post_1492_, v_usedLetOnly_boxed_1503_, v_skipConstInApp_boxed_1504_, v_skipInstances_boxed_1505_, v_e_1496_, v_a_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v_a_1497_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___boxed(lean_object* v_pre_1507_, lean_object* v_post_1508_, lean_object* v_usedLetOnly_1509_, lean_object* v_skipConstInApp_1510_, lean_object* v_skipInstances_1511_, lean_object* v_fvars_1512_, lean_object* v_e_1513_, lean_object* v_a_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
uint8_t v_usedLetOnly_boxed_1520_; uint8_t v_skipConstInApp_boxed_1521_; uint8_t v_skipInstances_boxed_1522_; lean_object* v_res_1523_; 
v_usedLetOnly_boxed_1520_ = lean_unbox(v_usedLetOnly_1509_);
v_skipConstInApp_boxed_1521_ = lean_unbox(v_skipConstInApp_1510_);
v_skipInstances_boxed_1522_ = lean_unbox(v_skipInstances_1511_);
v_res_1523_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1507_, v_post_1508_, v_usedLetOnly_boxed_1520_, v_skipConstInApp_boxed_1521_, v_skipInstances_boxed_1522_, v_fvars_1512_, v_e_1513_, v_a_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v_a_1514_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___boxed(lean_object* v_pre_1524_, lean_object* v_post_1525_, lean_object* v_usedLetOnly_1526_, lean_object* v_skipConstInApp_1527_, lean_object* v_skipInstances_1528_, lean_object* v_fvars_1529_, lean_object* v_e_1530_, lean_object* v_a_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
uint8_t v_usedLetOnly_boxed_1537_; uint8_t v_skipConstInApp_boxed_1538_; uint8_t v_skipInstances_boxed_1539_; lean_object* v_res_1540_; 
v_usedLetOnly_boxed_1537_ = lean_unbox(v_usedLetOnly_1526_);
v_skipConstInApp_boxed_1538_ = lean_unbox(v_skipConstInApp_1527_);
v_skipInstances_boxed_1539_ = lean_unbox(v_skipInstances_1528_);
v_res_1540_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_1524_, v_post_1525_, v_usedLetOnly_boxed_1537_, v_skipConstInApp_boxed_1538_, v_skipInstances_boxed_1539_, v_fvars_1529_, v_e_1530_, v_a_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v_a_1531_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___boxed(lean_object* v_pre_1541_, lean_object* v_post_1542_, lean_object* v_usedLetOnly_1543_, lean_object* v_skipConstInApp_1544_, lean_object* v_skipInstances_1545_, lean_object* v_fvars_1546_, lean_object* v_e_1547_, lean_object* v_a_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
uint8_t v_usedLetOnly_boxed_1554_; uint8_t v_skipConstInApp_boxed_1555_; uint8_t v_skipInstances_boxed_1556_; lean_object* v_res_1557_; 
v_usedLetOnly_boxed_1554_ = lean_unbox(v_usedLetOnly_1543_);
v_skipConstInApp_boxed_1555_ = lean_unbox(v_skipConstInApp_1544_);
v_skipInstances_boxed_1556_ = lean_unbox(v_skipInstances_1545_);
v_res_1557_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_1541_, v_post_1542_, v_usedLetOnly_boxed_1554_, v_skipConstInApp_boxed_1555_, v_skipInstances_boxed_1556_, v_fvars_1546_, v_e_1547_, v_a_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v_a_1548_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_upperBound_1558_, lean_object* v___x_1559_, lean_object* v_pre_1560_, lean_object* v_post_1561_, lean_object* v_usedLetOnly_1562_, lean_object* v_skipConstInApp_1563_, lean_object* v_skipInstances_1564_, lean_object* v_a_1565_, lean_object* v_b_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
uint8_t v_usedLetOnly_boxed_1573_; uint8_t v_skipConstInApp_boxed_1574_; uint8_t v_skipInstances_boxed_1575_; lean_object* v_res_1576_; 
v_usedLetOnly_boxed_1573_ = lean_unbox(v_usedLetOnly_1562_);
v_skipConstInApp_boxed_1574_ = lean_unbox(v_skipConstInApp_1563_);
v_skipInstances_boxed_1575_ = lean_unbox(v_skipInstances_1564_);
v_res_1576_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v_upperBound_1558_, v___x_1559_, v_pre_1560_, v_post_1561_, v_usedLetOnly_boxed_1573_, v_skipConstInApp_boxed_1574_, v_skipInstances_boxed_1575_, v_a_1565_, v_b_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___x_1559_);
lean_dec(v_upperBound_1558_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8___boxed(lean_object* v_skipInstances_1577_, lean_object* v_pre_1578_, lean_object* v_post_1579_, lean_object* v_usedLetOnly_1580_, lean_object* v_skipConstInApp_1581_, lean_object* v_x_1582_, lean_object* v_x_1583_, lean_object* v_x_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
uint8_t v_skipInstances_boxed_1591_; uint8_t v_usedLetOnly_boxed_1592_; uint8_t v_skipConstInApp_boxed_1593_; lean_object* v_res_1594_; 
v_skipInstances_boxed_1591_ = lean_unbox(v_skipInstances_1577_);
v_usedLetOnly_boxed_1592_ = lean_unbox(v_usedLetOnly_1580_);
v_skipConstInApp_boxed_1593_ = lean_unbox(v_skipConstInApp_1581_);
v_res_1594_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_boxed_1591_, v_pre_1578_, v_post_1579_, v_usedLetOnly_boxed_1592_, v_skipConstInApp_boxed_1593_, v_x_1582_, v_x_1583_, v_x_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
return v_res_1594_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1595_ = lean_box(0);
v___x_1596_ = lean_unsigned_to_nat(16u);
v___x_1597_ = lean_mk_array(v___x_1596_, v___x_1595_);
return v___x_1597_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1598_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0);
v___x_1599_ = lean_unsigned_to_nat(0u);
v___x_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
lean_ctor_set(v___x_1600_, 1, v___x_1598_);
return v___x_1600_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_1602_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1602_, 0, lean_box(0));
lean_closure_set(v___x_1602_, 1, lean_box(0));
lean_closure_set(v___x_1602_, 2, v___x_1601_);
return v___x_1602_;
}
}
lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(lean_object* v_input_1603_, lean_object* v_pre_1604_, lean_object* v_post_1605_, uint8_t v_usedLetOnly_1606_, uint8_t v_skipConstInApp_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
uint8_t v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v_a_1616_; lean_object* v___x_1617_; 
v___x_1613_ = 0;
v___x_1614_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
v___x_1615_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v___x_1614_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_a_1616_);
lean_dec_ref(v___x_1615_);
v___x_1617_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1604_, v_post_1605_, v_usedLetOnly_1606_, v_skipConstInApp_1607_, v___x_1613_, v_input_1603_, v_a_1616_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1618_);
lean_dec_ref_known(v___x_1617_, 1);
v___x_1619_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1619_, 0, lean_box(0));
lean_closure_set(v___x_1619_, 1, lean_box(0));
lean_closure_set(v___x_1619_, 2, v_a_1616_);
v___x_1620_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v___x_1619_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1627_ == 0)
{
lean_object* v_unused_1628_; 
v_unused_1628_ = lean_ctor_get(v___x_1620_, 0);
lean_dec(v_unused_1628_);
v___x_1622_ = v___x_1620_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_dec(v___x_1620_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 0, v_a_1618_);
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1618_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
else
{
lean_dec(v_a_1616_);
return v___x_1617_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_1603_ = stack[0].m_obj;
lean_object* v_pre_1604_ = stack[1].m_obj;
lean_object* v_post_1605_ = stack[2].m_obj;
uint8_t v_usedLetOnly_1606_ = stack[3].m_num;
uint8_t v_skipConstInApp_1607_ = stack[4].m_num;
lean_object* v___y_1608_ = stack[5].m_obj;
lean_object* v___y_1609_ = stack[6].m_obj;
lean_object* v___y_1610_ = stack[7].m_obj;
lean_object* v___y_1611_ = stack[8].m_obj;
lean_object* v_res_1629_;
v_res_1629_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_input_1603_, v_pre_1604_, v_post_1605_, v_usedLetOnly_1606_, v_skipConstInApp_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
stack->m_obj
 = v_res_1629_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___boxed(lean_object* v_input_1630_, lean_object* v_pre_1631_, lean_object* v_post_1632_, lean_object* v_usedLetOnly_1633_, lean_object* v_skipConstInApp_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
uint8_t v_usedLetOnly_boxed_1640_; uint8_t v_skipConstInApp_boxed_1641_; lean_object* v_res_1642_; 
v_usedLetOnly_boxed_1640_ = lean_unbox(v_usedLetOnly_1633_);
v_skipConstInApp_boxed_1641_ = lean_unbox(v_skipConstInApp_1634_);
v_res_1642_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_input_1630_, v_pre_1631_, v_post_1632_, v_usedLetOnly_boxed_1640_, v_skipConstInApp_boxed_1641_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
return v_res_1642_;
}
}
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object* v_e_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_){
_start:
{
lean_object* v___f_1651_; lean_object* v___x_1652_; lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1664_; 
v___f_1651_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducible___closed__0));
v___x_1652_ = l_Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_1645_, v_a_1649_);
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1655_ = v___x_1652_;
v_isShared_1656_ = v_isSharedCheck_1664_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1652_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1664_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
uint8_t v___x_1657_; 
v___x_1657_ = lean_unbox(v_a_1653_);
lean_dec(v_a_1653_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1659_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v_e_1645_);
v___x_1659_ = v___x_1655_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_e_1645_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
else
{
uint8_t v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
lean_del_object(v___x_1655_);
v___x_1661_ = 0;
v___x_1662_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducible___closed__1));
v___x_1663_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_e_1645_, v___x_1662_, v___f_1651_, v___x_1661_, v___x_1661_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_);
return v___x_1663_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_unfoldReducible_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1645_ = stack[0].m_obj;
lean_object* v_a_1646_ = stack[1].m_obj;
lean_object* v_a_1647_ = stack[2].m_obj;
lean_object* v_a_1648_ = stack[3].m_obj;
lean_object* v_a_1649_ = stack[4].m_obj;
lean_object* v_res_1665_;
v_res_1665_ = l_Lean_Meta_Sym_unfoldReducible(v_e_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_);
stack->m_obj
 = v_res_1665_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___boxed(lean_object* v_e_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_Meta_Sym_unfoldReducible(v_e_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
lean_dec(v_a_1668_);
lean_dec_ref(v_a_1667_);
return v_res_1672_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(lean_object* v_upperBound_1673_, lean_object* v___x_1674_, lean_object* v_pre_1675_, lean_object* v_post_1676_, uint8_t v_usedLetOnly_1677_, uint8_t v_skipConstInApp_1678_, uint8_t v_skipInstances_1679_, lean_object* v___x_1680_, lean_object* v_inst_1681_, lean_object* v_R_1682_, lean_object* v_a_1683_, lean_object* v_b_1684_, lean_object* v_c_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v_upperBound_1673_, v___x_1674_, v_pre_1675_, v_post_1676_, v_usedLetOnly_1677_, v_skipConstInApp_1678_, v_skipInstances_1679_, v_a_1683_, v_b_1684_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
return v___x_1692_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1673_ = stack[0].m_obj;
lean_object* v___x_1674_ = stack[1].m_obj;
lean_object* v_pre_1675_ = stack[2].m_obj;
lean_object* v_post_1676_ = stack[3].m_obj;
uint8_t v_usedLetOnly_1677_ = stack[4].m_num;
uint8_t v_skipConstInApp_1678_ = stack[5].m_num;
uint8_t v_skipInstances_1679_ = stack[6].m_num;
lean_object* v___x_1680_ = stack[7].m_obj;
lean_object* v_a_1683_ = stack[10].m_obj;
lean_object* v_b_1684_ = stack[11].m_obj;
lean_object* v___y_1686_ = stack[13].m_obj;
lean_object* v___y_1687_ = stack[14].m_obj;
lean_object* v___y_1688_ = stack[15].m_obj;
lean_object* v___y_1689_ = stack[16].m_obj;
lean_object* v___y_1690_ = stack[17].m_obj;
lean_object* v_res_1693_;
v_res_1693_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_upperBound_1673_, v___x_1674_, v_pre_1675_, v_post_1676_, v_usedLetOnly_1677_, v_skipConstInApp_1678_, v_skipInstances_1679_, v___x_1680_, lean_box(0), lean_box(0), v_a_1683_, v_b_1684_, lean_box(0), v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
stack->m_obj
 = v_res_1693_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_1694_ = _args[0];
lean_object* v___x_1695_ = _args[1];
lean_object* v_pre_1696_ = _args[2];
lean_object* v_post_1697_ = _args[3];
lean_object* v_usedLetOnly_1698_ = _args[4];
lean_object* v_skipConstInApp_1699_ = _args[5];
lean_object* v_skipInstances_1700_ = _args[6];
lean_object* v___x_1701_ = _args[7];
lean_object* v_inst_1702_ = _args[8];
lean_object* v_R_1703_ = _args[9];
lean_object* v_a_1704_ = _args[10];
lean_object* v_b_1705_ = _args[11];
lean_object* v_c_1706_ = _args[12];
lean_object* v___y_1707_ = _args[13];
lean_object* v___y_1708_ = _args[14];
lean_object* v___y_1709_ = _args[15];
lean_object* v___y_1710_ = _args[16];
lean_object* v___y_1711_ = _args[17];
lean_object* v___y_1712_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_1713_; uint8_t v_skipConstInApp_boxed_1714_; uint8_t v_skipInstances_boxed_1715_; lean_object* v_res_1716_; 
v_usedLetOnly_boxed_1713_ = lean_unbox(v_usedLetOnly_1698_);
v_skipConstInApp_boxed_1714_ = lean_unbox(v_skipConstInApp_1699_);
v_skipInstances_boxed_1715_ = lean_unbox(v_skipInstances_1700_);
v_res_1716_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_upperBound_1694_, v___x_1695_, v_pre_1696_, v_post_1697_, v_usedLetOnly_boxed_1713_, v_skipConstInApp_boxed_1714_, v_skipInstances_boxed_1715_, v___x_1701_, v_inst_1702_, v_R_1703_, v_a_1704_, v_b_1705_, v_c_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec(v___x_1701_);
lean_dec_ref(v___x_1695_);
lean_dec(v_upperBound_1694_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_1717_, lean_object* v_m_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_m_1718_, v_a_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_1721_, lean_object* v_m_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(v_00_u03b2_1721_, v_m_1722_, v_a_1723_);
lean_dec_ref(v_a_1723_);
lean_dec_ref(v_m_1722_);
return v_res_1724_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1725_, lean_object* v_name_1726_, uint8_t v_bi_1727_, lean_object* v_type_1728_, lean_object* v_k_1729_, uint8_t v_kind_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_1726_, v_bi_1727_, v_type_1728_, v_k_1729_, v_kind_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
return v___x_1737_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1726_ = stack[1].m_obj;
uint8_t v_bi_1727_ = stack[2].m_num;
lean_object* v_type_1728_ = stack[3].m_obj;
lean_object* v_k_1729_ = stack[4].m_obj;
uint8_t v_kind_1730_ = stack[5].m_num;
lean_object* v___y_1731_ = stack[6].m_obj;
lean_object* v___y_1732_ = stack[7].m_obj;
lean_object* v___y_1733_ = stack[8].m_obj;
lean_object* v___y_1734_ = stack[9].m_obj;
lean_object* v___y_1735_ = stack[10].m_obj;
lean_object* v_res_1738_;
v_res_1738_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(lean_box(0), v_name_1726_, v_bi_1727_, v_type_1728_, v_k_1729_, v_kind_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
stack->m_obj
 = v_res_1738_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1739_, lean_object* v_name_1740_, lean_object* v_bi_1741_, lean_object* v_type_1742_, lean_object* v_k_1743_, lean_object* v_kind_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
uint8_t v_bi_boxed_1751_; uint8_t v_kind_boxed_1752_; lean_object* v_res_1753_; 
v_bi_boxed_1751_ = lean_unbox(v_bi_1741_);
v_kind_boxed_1752_ = lean_unbox(v_kind_1744_);
v_res_1753_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1739_, v_name_1740_, v_bi_boxed_1751_, v_type_1742_, v_k_1743_, v_kind_boxed_1752_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
return v_res_1753_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(lean_object* v_00_u03b1_1754_, lean_object* v_name_1755_, lean_object* v_type_1756_, lean_object* v_val_1757_, lean_object* v_k_1758_, uint8_t v_nondep_1759_, uint8_t v_kind_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_1755_, v_type_1756_, v_val_1757_, v_k_1758_, v_nondep_1759_, v_kind_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
return v___x_1767_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1755_ = stack[1].m_obj;
lean_object* v_type_1756_ = stack[2].m_obj;
lean_object* v_val_1757_ = stack[3].m_obj;
lean_object* v_k_1758_ = stack[4].m_obj;
uint8_t v_nondep_1759_ = stack[5].m_num;
uint8_t v_kind_1760_ = stack[6].m_num;
lean_object* v___y_1761_ = stack[7].m_obj;
lean_object* v___y_1762_ = stack[8].m_obj;
lean_object* v___y_1763_ = stack[9].m_obj;
lean_object* v___y_1764_ = stack[10].m_obj;
lean_object* v___y_1765_ = stack[11].m_obj;
lean_object* v_res_1768_;
v_res_1768_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(lean_box(0), v_name_1755_, v_type_1756_, v_val_1757_, v_k_1758_, v_nondep_1759_, v_kind_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
stack->m_obj
 = v_res_1768_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1769_, lean_object* v_name_1770_, lean_object* v_type_1771_, lean_object* v_val_1772_, lean_object* v_k_1773_, lean_object* v_nondep_1774_, lean_object* v_kind_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
uint8_t v_nondep_boxed_1782_; uint8_t v_kind_boxed_1783_; lean_object* v_res_1784_; 
v_nondep_boxed_1782_ = lean_unbox(v_nondep_1774_);
v_kind_boxed_1783_ = lean_unbox(v_kind_1775_);
v_res_1784_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_1769_, v_name_1770_, v_type_1771_, v_val_1772_, v_k_1773_, v_nondep_boxed_1782_, v_kind_boxed_1783_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
return v_res_1784_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(lean_object* v_00_u03b1_1785_, lean_object* v_ref_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1786_);
return v___x_1792_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1786_ = stack[1].m_obj;
lean_object* v___y_1787_ = stack[2].m_obj;
lean_object* v___y_1788_ = stack[3].m_obj;
lean_object* v___y_1789_ = stack[4].m_obj;
lean_object* v___y_1790_ = stack[5].m_obj;
lean_object* v_res_1793_;
v_res_1793_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(lean_box(0), v_ref_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
stack->m_obj
 = v_res_1793_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___boxed(lean_object* v_00_u03b1_1794_, lean_object* v_ref_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_1794_, v_ref_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
return v_res_1801_;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(lean_object* v_00_u03b1_1802_, lean_object* v_x_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
return v___x_1810_;
}
}
LEAN_EXPORT void l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1803_ = stack[1].m_obj;
lean_object* v___y_1804_ = stack[2].m_obj;
lean_object* v___y_1805_ = stack[3].m_obj;
lean_object* v___y_1806_ = stack[4].m_obj;
lean_object* v___y_1807_ = stack[5].m_obj;
lean_object* v___y_1808_ = stack[6].m_obj;
lean_object* v_res_1811_;
v_res_1811_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(lean_box(0), v_x_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
stack->m_obj
 = v_res_1811_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___boxed(lean_object* v_00_u03b1_1812_, lean_object* v_x_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(v_00_u03b1_1812_, v_x_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10(lean_object* v_00_u03b2_1821_, lean_object* v_m_1822_, lean_object* v_a_1823_, lean_object* v_b_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v_m_1822_, v_a_1823_, v_b_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(lean_object* v_00_u03b2_1826_, lean_object* v_a_1827_, lean_object* v_x_1828_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1827_, v_x_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_00_u03b2_1830_, lean_object* v_a_1831_, lean_object* v_x_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_1830_, v_a_1831_, v_x_1832_);
lean_dec(v_x_1832_);
lean_dec_ref(v_a_1831_);
return v_res_1833_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(lean_object* v_00_u03b2_1834_, lean_object* v_a_1835_, lean_object* v_x_1836_){
_start:
{
uint8_t v___x_1837_; 
v___x_1837_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_1835_, v_x_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1835_ = stack[1].m_obj;
lean_object* v_x_1836_ = stack[2].m_obj;
uint8_t v_res_1838_;
v_res_1838_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(lean_box(0), v_a_1835_, v_x_1836_);
stack->m_num = v_res_1838_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___boxed(lean_object* v_00_u03b2_1839_, lean_object* v_a_1840_, lean_object* v_x_1841_){
_start:
{
uint8_t v_res_1842_; lean_object* v_r_1843_; 
v_res_1842_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_1839_, v_a_1840_, v_x_1841_);
lean_dec(v_x_1841_);
lean_dec_ref(v_a_1840_);
v_r_1843_ = lean_box(v_res_1842_);
return v_r_1843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16(lean_object* v_00_u03b2_1844_, lean_object* v_data_1845_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(v_data_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17(lean_object* v_00_u03b2_1847_, lean_object* v_a_1848_, lean_object* v_b_1849_, lean_object* v_x_1850_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_1848_, v_b_1849_, v_x_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object* v_00_u03b2_1852_, lean_object* v_i_1853_, lean_object* v_source_1854_, lean_object* v_target_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_1853_, v_source_1854_, v_target_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object* v_00_u03b2_1857_, lean_object* v_x_1858_, lean_object* v_x_1859_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_1858_, v_x_1859_);
return v___x_1860_;
}
}
lean_object* l_Lean_Meta_Sym_foldProjs___lam__0(lean_object* v_x_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1867_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_foldProjs___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1861_ = stack[0].m_obj;
lean_object* v___y_1862_ = stack[1].m_obj;
lean_object* v___y_1863_ = stack[2].m_obj;
lean_object* v___y_1864_ = stack[3].m_obj;
lean_object* v___y_1865_ = stack[4].m_obj;
lean_object* v_res_1869_;
v_res_1869_ = l_Lean_Meta_Sym_foldProjs___lam__0(v_x_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
stack->m_obj
 = v_res_1869_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___boxed(lean_object* v_x_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_Meta_Sym_foldProjs___lam__0(v_x_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec_ref(v_x_1870_);
return v_res_1876_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(lean_object* v_msgData_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v___x_1883_; lean_object* v_env_1884_; uint8_t v___x_1885_; lean_object* v_env_1886_; lean_object* v___x_1887_; lean_object* v_toCold_1888_; lean_object* v_mctx_1889_; lean_object* v_lctx_1890_; lean_object* v_options_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1883_ = lean_st_ref_get(v___y_1881_);
v_env_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc_ref(v_env_1884_);
lean_dec(v___x_1883_);
v___x_1885_ = 0;
v_env_1886_ = l_Lean_Environment_setRecordingDeps(v_env_1884_, v___x_1885_);
v___x_1887_ = lean_st_ref_get(v___y_1879_);
v_toCold_1888_ = lean_ctor_get(v___y_1880_, 0);
v_mctx_1889_ = lean_ctor_get(v___x_1887_, 0);
lean_inc_ref(v_mctx_1889_);
lean_dec(v___x_1887_);
v_lctx_1890_ = lean_ctor_get(v___y_1878_, 2);
v_options_1891_ = lean_ctor_get(v_toCold_1888_, 2);
lean_inc_ref(v_options_1891_);
lean_inc_ref(v_lctx_1890_);
v___x_1892_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1892_, 0, v_env_1886_);
lean_ctor_set(v___x_1892_, 1, v_mctx_1889_);
lean_ctor_set(v___x_1892_, 2, v_lctx_1890_);
lean_ctor_set(v___x_1892_, 3, v_options_1891_);
v___x_1893_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
lean_ctor_set(v___x_1893_, 1, v_msgData_1877_);
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1877_ = stack[0].m_obj;
lean_object* v___y_1878_ = stack[1].m_obj;
lean_object* v___y_1879_ = stack[2].m_obj;
lean_object* v___y_1880_ = stack[3].m_obj;
lean_object* v___y_1881_ = stack[4].m_obj;
lean_object* v_res_1895_;
v_res_1895_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msgData_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
stack->m_obj
 = v_res_1895_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0___boxed(lean_object* v_msgData_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msgData_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
return v_res_1902_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1903_; double v___x_1904_; 
v___x_1903_ = lean_unsigned_to_nat(0u);
v___x_1904_ = lean_float_of_nat(v___x_1903_);
return v___x_1904_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(lean_object* v_cls_1908_, lean_object* v_msg_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_ref_1915_; lean_object* v___x_1916_; lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1962_; 
v_ref_1915_ = lean_ctor_get(v___y_1912_, 2);
v___x_1916_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1919_ = v___x_1916_;
v_isShared_1920_ = v_isSharedCheck_1962_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1916_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1962_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; lean_object* v_traceState_1922_; lean_object* v_env_1923_; lean_object* v_nextMacroScope_1924_; lean_object* v_ngen_1925_; lean_object* v_auxDeclNGen_1926_; lean_object* v_cache_1927_; lean_object* v_recordedDeps_1928_; lean_object* v_messages_1929_; lean_object* v_infoState_1930_; lean_object* v_snapshotTasks_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1961_; 
v___x_1921_ = lean_st_ref_take(v___y_1913_);
v_traceState_1922_ = lean_ctor_get(v___x_1921_, 4);
v_env_1923_ = lean_ctor_get(v___x_1921_, 0);
v_nextMacroScope_1924_ = lean_ctor_get(v___x_1921_, 1);
v_ngen_1925_ = lean_ctor_get(v___x_1921_, 2);
v_auxDeclNGen_1926_ = lean_ctor_get(v___x_1921_, 3);
v_cache_1927_ = lean_ctor_get(v___x_1921_, 5);
v_recordedDeps_1928_ = lean_ctor_get(v___x_1921_, 6);
v_messages_1929_ = lean_ctor_get(v___x_1921_, 7);
v_infoState_1930_ = lean_ctor_get(v___x_1921_, 8);
v_snapshotTasks_1931_ = lean_ctor_get(v___x_1921_, 9);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1933_ = v___x_1921_;
v_isShared_1934_ = v_isSharedCheck_1961_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_snapshotTasks_1931_);
lean_inc(v_infoState_1930_);
lean_inc(v_messages_1929_);
lean_inc(v_recordedDeps_1928_);
lean_inc(v_cache_1927_);
lean_inc(v_traceState_1922_);
lean_inc(v_auxDeclNGen_1926_);
lean_inc(v_ngen_1925_);
lean_inc(v_nextMacroScope_1924_);
lean_inc(v_env_1923_);
lean_dec(v___x_1921_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1961_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
uint64_t v_tid_1935_; lean_object* v_traces_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1960_; 
v_tid_1935_ = lean_ctor_get_uint64(v_traceState_1922_, sizeof(void*)*1);
v_traces_1936_ = lean_ctor_get(v_traceState_1922_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v_traceState_1922_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1938_ = v_traceState_1922_;
v_isShared_1939_ = v_isSharedCheck_1960_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_traces_1936_);
lean_dec(v_traceState_1922_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1960_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; double v___x_1942_; uint8_t v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1951_; 
v___x_1940_ = lean_box(0);
v___x_1941_ = lean_box(0);
v___x_1942_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_1943_ = 0;
v___x_1944_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_1945_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1945_, 0, v_cls_1908_);
lean_ctor_set(v___x_1945_, 1, v___x_1941_);
lean_ctor_set(v___x_1945_, 2, v___x_1944_);
lean_ctor_set_float(v___x_1945_, sizeof(void*)*3, v___x_1942_);
lean_ctor_set_float(v___x_1945_, sizeof(void*)*3 + 8, v___x_1942_);
lean_ctor_set_uint8(v___x_1945_, sizeof(void*)*3 + 16, v___x_1943_);
v___x_1946_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
v___x_1947_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1945_);
lean_ctor_set(v___x_1947_, 1, v_a_1917_);
lean_ctor_set(v___x_1947_, 2, v___x_1946_);
lean_inc(v_ref_1915_);
v___x_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1948_, 0, v_ref_1915_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = l_Lean_PersistentArray_push___redArg(v_traces_1936_, v___x_1948_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v___x_1949_);
v___x_1951_ = v___x_1938_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1949_);
lean_ctor_set_uint64(v_reuseFailAlloc_1959_, sizeof(void*)*1, v_tid_1935_);
v___x_1951_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
lean_object* v___x_1953_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 4, v___x_1951_);
v___x_1953_ = v___x_1933_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_env_1923_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_nextMacroScope_1924_);
lean_ctor_set(v_reuseFailAlloc_1958_, 2, v_ngen_1925_);
lean_ctor_set(v_reuseFailAlloc_1958_, 3, v_auxDeclNGen_1926_);
lean_ctor_set(v_reuseFailAlloc_1958_, 4, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_1958_, 5, v_cache_1927_);
lean_ctor_set(v_reuseFailAlloc_1958_, 6, v_recordedDeps_1928_);
lean_ctor_set(v_reuseFailAlloc_1958_, 7, v_messages_1929_);
lean_ctor_set(v_reuseFailAlloc_1958_, 8, v_infoState_1930_);
lean_ctor_set(v_reuseFailAlloc_1958_, 9, v_snapshotTasks_1931_);
v___x_1953_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
lean_object* v___x_1954_; lean_object* v___x_1956_; 
v___x_1954_ = lean_st_ref_put(v___y_1913_, v___x_1953_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v___x_1940_);
v___x_1956_ = v___x_1919_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1940_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1908_ = stack[0].m_obj;
lean_object* v_msg_1909_ = stack[1].m_obj;
lean_object* v___y_1910_ = stack[2].m_obj;
lean_object* v___y_1911_ = stack[3].m_obj;
lean_object* v___y_1912_ = stack[4].m_obj;
lean_object* v___y_1913_ = stack[5].m_obj;
lean_object* v_res_1963_;
v_res_1963_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v_cls_1908_, v_msg_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
stack->m_obj
 = v_res_1963_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___boxed(lean_object* v_cls_1964_, lean_object* v_msg_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v_cls_1964_, v_msg_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
return v_res_1971_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1975_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_1976_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__1));
v___x_1977_ = l_Lean_Name_append(v___x_1976_, v___x_1975_);
return v___x_1977_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__3));
v___x_1980_ = l_Lean_stringToMessageData(v___x_1979_);
return v___x_1980_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__5));
v___x_1983_ = l_Lean_stringToMessageData(v___x_1982_);
return v___x_1983_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__8(void){
_start:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__7));
v___x_1986_ = l_Lean_stringToMessageData(v___x_1985_);
return v___x_1986_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__10(void){
_start:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1988_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__1___closed__9));
v___x_1989_ = l_Lean_stringToMessageData(v___x_1988_);
return v___x_1989_;
}
}
lean_object* l_Lean_Meta_Sym_foldProjs___lam__1(lean_object* v_e_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v___y_1997_; 
if (lean_obj_tag(v_e_1990_) == 11)
{
lean_object* v_typeName_2021_; lean_object* v_idx_2022_; lean_object* v_struct_2023_; lean_object* v___x_2024_; lean_object* v_env_2025_; lean_object* v___x_2026_; 
v_typeName_2021_ = lean_ctor_get(v_e_1990_, 0);
v_idx_2022_ = lean_ctor_get(v_e_1990_, 1);
v_struct_2023_ = lean_ctor_get(v_e_1990_, 2);
v___x_2024_ = lean_st_ref_get(v___y_1994_);
v_env_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc_ref(v_env_2025_);
lean_dec(v___x_2024_);
lean_inc(v_typeName_2021_);
v___x_2026_ = l_Lean_getStructureInfo_x3f(v_env_2025_, v_typeName_2021_);
if (lean_obj_tag(v___x_2026_) == 1)
{
lean_object* v_val_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2081_; 
v_val_2027_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2029_ = v___x_2026_;
v_isShared_2030_ = v_isSharedCheck_2081_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_val_2027_);
lean_dec(v___x_2026_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2081_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v_fieldNames_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v_fieldNames_2031_ = lean_ctor_get(v_val_2027_, 1);
lean_inc_ref(v_fieldNames_2031_);
lean_dec(v_val_2027_);
v___x_2032_ = lean_array_get_size(v_fieldNames_2031_);
v___x_2033_ = lean_nat_dec_lt(v_idx_2022_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_object* v_toCold_2034_; lean_object* v_options_2035_; uint8_t v_hasTrace_2036_; 
lean_dec_ref(v_fieldNames_2031_);
v_toCold_2034_ = lean_ctor_get(v___y_1993_, 0);
v_options_2035_ = lean_ctor_get(v_toCold_2034_, 2);
v_hasTrace_2036_ = lean_ctor_get_uint8(v_options_2035_, sizeof(void*)*1);
if (v_hasTrace_2036_ == 0)
{
lean_del_object(v___x_2029_);
goto v___jp_2018_;
}
else
{
lean_object* v_inheritedTraceOptions_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; 
v_inheritedTraceOptions_2037_ = lean_ctor_get(v_toCold_2034_, 11);
v___x_2038_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_2039_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__2);
v___x_2040_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2037_, v_options_2035_, v___x_2039_);
if (v___x_2040_ == 0)
{
lean_del_object(v___x_2029_);
goto v___jp_2018_;
}
else
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2041_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__4, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__4_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__4);
lean_inc(v_idx_2022_);
v___x_2042_ = l_Nat_reprFast(v_idx_2022_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set_tag(v___x_2029_, 3);
lean_ctor_set(v___x_2029_, 0, v___x_2042_);
v___x_2044_ = v___x_2029_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2045_ = l_Lean_MessageData_ofFormat(v___x_2044_);
v___x_2046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2041_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__6, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__6_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__6);
v___x_2048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2046_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
lean_inc_ref(v_e_1990_);
v___x_2049_ = l_Lean_indentExpr(v_e_1990_);
v___x_2050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2048_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
v___x_2051_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v___x_2038_, v___x_2050_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_dec_ref_known(v___x_2051_, 1);
goto v___jp_2018_;
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec_ref_known(v_e_1990_, 3);
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2051_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2051_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2061_; uint8_t v_transparency_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; uint8_t v___x_2065_; 
lean_inc_ref(v_struct_2023_);
lean_inc(v_idx_2022_);
lean_del_object(v___x_2029_);
lean_dec_ref_known(v_e_1990_, 3);
v___x_2061_ = l_Lean_Meta_Context_config(v___y_1991_);
v_transparency_2062_ = lean_ctor_get_uint8(v___x_2061_, 9);
lean_dec_ref(v___x_2061_);
v___x_2063_ = lean_array_fget(v_fieldNames_2031_, v_idx_2022_);
lean_dec(v_idx_2022_);
lean_dec_ref(v_fieldNames_2031_);
v___x_2064_ = 1;
v___x_2065_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2062_, v___x_2064_);
if (v___x_2065_ == 0)
{
lean_object* v_keyedConfig_2066_; uint8_t v_trackZetaDelta_2067_; lean_object* v_zetaDeltaSet_2068_; lean_object* v_lctx_2069_; lean_object* v_localInstances_2070_; lean_object* v_defEqCtx_x3f_2071_; lean_object* v_synthPendingDepth_2072_; lean_object* v_customCanUnfoldPredicate_x3f_2073_; uint8_t v_univApprox_2074_; uint8_t v_inTypeClassResolution_2075_; uint8_t v_cacheInferType_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v_keyedConfig_2066_ = lean_ctor_get(v___y_1991_, 0);
v_trackZetaDelta_2067_ = lean_ctor_get_uint8(v___y_1991_, sizeof(void*)*7);
v_zetaDeltaSet_2068_ = lean_ctor_get(v___y_1991_, 1);
v_lctx_2069_ = lean_ctor_get(v___y_1991_, 2);
v_localInstances_2070_ = lean_ctor_get(v___y_1991_, 3);
v_defEqCtx_x3f_2071_ = lean_ctor_get(v___y_1991_, 4);
v_synthPendingDepth_2072_ = lean_ctor_get(v___y_1991_, 5);
v_customCanUnfoldPredicate_x3f_2073_ = lean_ctor_get(v___y_1991_, 6);
v_univApprox_2074_ = lean_ctor_get_uint8(v___y_1991_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2075_ = lean_ctor_get_uint8(v___y_1991_, sizeof(void*)*7 + 2);
v_cacheInferType_2076_ = lean_ctor_get_uint8(v___y_1991_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2066_);
v___x_2077_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2064_, v_keyedConfig_2066_);
lean_inc(v_customCanUnfoldPredicate_x3f_2073_);
lean_inc(v_synthPendingDepth_2072_);
lean_inc(v_defEqCtx_x3f_2071_);
lean_inc_ref(v_localInstances_2070_);
lean_inc_ref(v_lctx_2069_);
lean_inc(v_zetaDeltaSet_2068_);
v___x_2078_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
lean_ctor_set(v___x_2078_, 1, v_zetaDeltaSet_2068_);
lean_ctor_set(v___x_2078_, 2, v_lctx_2069_);
lean_ctor_set(v___x_2078_, 3, v_localInstances_2070_);
lean_ctor_set(v___x_2078_, 4, v_defEqCtx_x3f_2071_);
lean_ctor_set(v___x_2078_, 5, v_synthPendingDepth_2072_);
lean_ctor_set(v___x_2078_, 6, v_customCanUnfoldPredicate_x3f_2073_);
lean_ctor_set_uint8(v___x_2078_, sizeof(void*)*7, v_trackZetaDelta_2067_);
lean_ctor_set_uint8(v___x_2078_, sizeof(void*)*7 + 1, v_univApprox_2074_);
lean_ctor_set_uint8(v___x_2078_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2075_);
lean_ctor_set_uint8(v___x_2078_, sizeof(void*)*7 + 3, v_cacheInferType_2076_);
v___x_2079_ = l_Lean_Meta_mkProjection(v_struct_2023_, v___x_2063_, v___x_2078_, v___y_1992_, v___y_1993_, v___y_1994_);
lean_dec_ref_known(v___x_2078_, 7);
v___y_1997_ = v___x_2079_;
goto v___jp_1996_;
}
else
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Lean_Meta_mkProjection(v_struct_2023_, v___x_2063_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
v___y_1997_ = v___x_2080_;
goto v___jp_1996_;
}
}
}
}
else
{
lean_object* v_toCold_2082_; lean_object* v_options_2083_; uint8_t v_hasTrace_2084_; 
lean_dec(v___x_2026_);
v_toCold_2082_ = lean_ctor_get(v___y_1993_, 0);
v_options_2083_ = lean_ctor_get(v_toCold_2082_, 2);
v_hasTrace_2084_ = lean_ctor_get_uint8(v_options_2083_, sizeof(void*)*1);
if (v_hasTrace_2084_ == 0)
{
goto v___jp_2015_;
}
else
{
lean_object* v_inheritedTraceOptions_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; 
v_inheritedTraceOptions_2085_ = lean_ctor_get(v_toCold_2082_, 11);
v___x_2086_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_2087_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__2);
v___x_2088_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2085_, v_options_2083_, v___x_2087_);
if (v___x_2088_ == 0)
{
goto v___jp_2015_;
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2089_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__8, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__8_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__8);
lean_inc(v_typeName_2021_);
v___x_2090_ = l_Lean_MessageData_ofName(v_typeName_2021_);
v___x_2091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2089_);
lean_ctor_set(v___x_2091_, 1, v___x_2090_);
v___x_2092_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__10, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__10_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__10);
v___x_2093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2091_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
lean_inc_ref(v_e_1990_);
v___x_2094_ = l_Lean_indentExpr(v_e_1990_);
v___x_2095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2093_);
lean_ctor_set(v___x_2095_, 1, v___x_2094_);
v___x_2096_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v___x_2086_, v___x_2095_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_dec_ref_known(v___x_2096_, 1);
goto v___jp_2015_;
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec_ref_known(v_e_1990_, 3);
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2096_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2096_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2105_, 0, v_e_1990_);
v___x_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
return v___x_2106_;
}
v___jp_1996_:
{
if (lean_obj_tag(v___y_1997_) == 0)
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2006_; 
v_a_1998_ = lean_ctor_get(v___y_1997_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___y_1997_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2000_ = v___y_1997_;
v_isShared_2001_ = v_isSharedCheck_2006_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___y_1997_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2006_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; lean_object* v___x_2004_; 
v___x_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2002_, 0, v_a_1998_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 0, v___x_2002_);
v___x_2004_ = v___x_2000_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
v_a_2007_ = lean_ctor_get(v___y_1997_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___y_1997_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___y_1997_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___y_1997_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
v___jp_2015_:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2016_, 0, v_e_1990_);
v___x_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
return v___x_2017_;
}
v___jp_2018_:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2019_, 0, v_e_1990_);
v___x_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
return v___x_2020_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_foldProjs___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1990_ = stack[0].m_obj;
lean_object* v___y_1991_ = stack[1].m_obj;
lean_object* v___y_1992_ = stack[2].m_obj;
lean_object* v___y_1993_ = stack[3].m_obj;
lean_object* v___y_1994_ = stack[4].m_obj;
lean_object* v_res_2107_;
v_res_2107_ = l_Lean_Meta_Sym_foldProjs___lam__1(v_e_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
stack->m_obj
 = v_res_2107_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___boxed(lean_object* v_e_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_Lean_Meta_Sym_foldProjs___lam__1(v_e_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
return v_res_2114_;
}
}
lean_object* l_Lean_Meta_Sym_foldProjs(lean_object* v_e_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_){
_start:
{
lean_object* v___f_2124_; lean_object* v___x_2125_; 
v___f_2124_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__0));
v___x_2125_ = lean_find_expr(v___f_2124_, v_e_2118_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v___x_2126_; 
v___x_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2126_, 0, v_e_2118_);
return v___x_2126_;
}
else
{
lean_object* v___f_2127_; lean_object* v_post_2128_; uint8_t v___x_2129_; lean_object* v___x_2130_; 
lean_dec_ref_known(v___x_2125_, 1);
v___f_2127_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__1));
v_post_2128_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__2));
v___x_2129_ = 0;
v___x_2130_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_e_2118_, v___f_2127_, v_post_2128_, v___x_2129_, v___x_2129_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
return v___x_2130_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_foldProjs_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2118_ = stack[0].m_obj;
lean_object* v_a_2119_ = stack[1].m_obj;
lean_object* v_a_2120_ = stack[2].m_obj;
lean_object* v_a_2121_ = stack[3].m_obj;
lean_object* v_a_2122_ = stack[4].m_obj;
lean_object* v_res_2131_;
v_res_2131_ = l_Lean_Meta_Sym_foldProjs(v_e_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
stack->m_obj
 = v_res_2131_;
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
uint8_t l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(lean_object* v_opts_2280_, lean_object* v_opt_2281_){
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
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_2280_ = stack[0].m_obj;
lean_object* v_opt_2281_ = stack[1].m_obj;
uint8_t v_res_2290_;
v_res_2290_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(v_opts_2280_, v_opt_2281_);
stack->m_num = v_res_2290_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0___boxed(lean_object* v_opts_2291_, lean_object* v_opt_2292_){
_start:
{
uint8_t v_res_2293_; lean_object* v_r_2294_; 
v_res_2293_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(v_opts_2291_, v_opt_2292_);
lean_dec_ref(v_opt_2292_);
lean_dec_ref(v_opts_2291_);
v_r_2294_ = lean_box(v_res_2293_);
return v_r_2294_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2295_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2296_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0);
v___x_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
return v___x_2297_;
}
}
lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg(){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__1);
return v___x_2299_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2300_;
v_res_2300_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg();
stack->m_obj
 = v_res_2300_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___boxed(lean_object* v___dummy_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg();
return v_res_2302_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg();
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1(lean_object* v_00_u03b2_2304_){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0);
return v___x_2305_;
}
}
lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(lean_object* v_msg_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v___f_2313_; lean_object* v___x_2166__overap_2314_; lean_object* v___x_2315_; 
v___f_2313_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___closed__0));
v___x_2166__overap_2314_ = lean_panic_fn_borrowed(v___f_2313_, v_msg_2307_);
lean_inc(v___y_2311_);
lean_inc_ref(v___y_2310_);
lean_inc(v___y_2309_);
lean_inc_ref(v___y_2308_);
v___x_2315_ = lean_apply_5(v___x_2166__overap_2314_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, lean_box(0));
return v___x_2315_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2307_ = stack[0].m_obj;
lean_object* v___y_2308_ = stack[1].m_obj;
lean_object* v___y_2309_ = stack[2].m_obj;
lean_object* v___y_2310_ = stack[3].m_obj;
lean_object* v___y_2311_ = stack[4].m_obj;
lean_object* v_res_2316_;
v_res_2316_ = l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(v_msg_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
stack->m_obj
 = v_res_2316_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2___boxed(lean_object* v_msg_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(v_msg_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
return v_res_2323_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___redArg___closed__0);
v___x_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2324_);
return v___x_2325_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
return v___x_2327_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__5(void){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2331_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__4));
v___x_2332_ = lean_unsigned_to_nat(19u);
v___x_2333_ = lean_unsigned_to_nat(307u);
v___x_2334_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__3));
v___x_2335_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__2));
v___x_2336_ = l_mkPanicMessageWithDecl(v___x_2335_, v___x_2334_, v___x_2333_, v___x_2332_, v___x_2331_);
return v___x_2336_;
}
}
lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object* v_x_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_){
_start:
{
lean_object* v_fst_2344_; lean_object* v_snd_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___x_2385_; lean_object* v_env_2386_; uint8_t v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2385_ = lean_st_ref_get(v_a_2341_);
v_env_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc_ref(v_env_2386_);
lean_dec(v___x_2385_);
v___x_2387_ = 0;
v___x_2388_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2388_, 0, v_env_2386_);
lean_ctor_set_uint8(v___x_2388_, sizeof(void*)*1, v___x_2387_);
lean_ctor_set_uint8(v___x_2388_, sizeof(void*)*1 + 1, v___x_2387_);
v___x_2389_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0);
v___x_2390_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(v___x_2388_, v___x_2389_);
lean_dec_ref_known(v___x_2388_, 1);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v_a_2392_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
v_a_2392_ = lean_ctor_get(v___x_2390_, 1);
lean_inc(v_a_2392_);
lean_dec_ref_known(v___x_2390_, 2);
v_fst_2344_ = v_a_2391_;
v_snd_2345_ = v_a_2392_;
v___y_2346_ = v_a_2338_;
v___y_2347_ = v_a_2339_;
v___y_2348_ = v_a_2340_;
v___y_2349_ = v_a_2341_;
goto v___jp_2343_;
}
else
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
lean_dec_ref_known(v___x_2390_, 2);
v___x_2393_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__5, &l_Lean_Meta_Sym_SymM_run___redArg___closed__5_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__5);
v___x_2394_ = l_panic___at___00Lean_Meta_Sym_SymM_run_spec__2(v___x_2393_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v_fst_2396_; lean_object* v_snd_2397_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
lean_dec_ref_known(v___x_2394_, 1);
v_fst_2396_ = lean_ctor_get(v_a_2395_, 0);
lean_inc(v_fst_2396_);
v_snd_2397_ = lean_ctor_get(v_a_2395_, 1);
lean_inc(v_snd_2397_);
lean_dec(v_a_2395_);
v_fst_2344_ = v_fst_2396_;
v_snd_2345_ = v_snd_2397_;
v___y_2346_ = v_a_2338_;
v___y_2347_ = v_a_2339_;
v___y_2348_ = v_a_2340_;
v___y_2349_ = v_a_2341_;
goto v___jp_2343_;
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
lean_dec_ref(v_x_2337_);
v_a_2398_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2394_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2394_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
v___jp_2343_:
{
lean_object* v_ref_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; uint8_t v___x_2353_; lean_object* v___x_2354_; 
v_ref_2350_ = lean_ctor_get(v___y_2348_, 2);
v___x_2351_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2348_);
v___x_2352_ = l_Lean_Meta_Sym_sym_debug;
v___x_2353_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__0(v___x_2351_, v___x_2352_);
lean_dec_ref(v___x_2351_);
v___x_2354_ = l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_a_2355_);
lean_dec_ref_known(v___x_2354_, 1);
v___x_2356_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedConfig_default___closed__0));
v___x_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2357_, 0, v_fst_2344_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
v___x_2358_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__0, &l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0);
v___x_2359_ = lean_box(0);
v___x_2360_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__1, &l_Lean_Meta_Sym_SymM_run___redArg___closed__1_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1);
v___x_2361_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v___x_2361_, 0, v_snd_2345_);
lean_ctor_set(v___x_2361_, 1, v___x_2358_);
lean_ctor_set(v___x_2361_, 2, v___x_2358_);
lean_ctor_set(v___x_2361_, 3, v___x_2358_);
lean_ctor_set(v___x_2361_, 4, v___x_2358_);
lean_ctor_set(v___x_2361_, 5, v___x_2358_);
lean_ctor_set(v___x_2361_, 6, v___x_2358_);
lean_ctor_set(v___x_2361_, 7, v___x_2358_);
lean_ctor_set(v___x_2361_, 8, v_a_2355_);
lean_ctor_set(v___x_2361_, 9, v___x_2359_);
lean_ctor_set(v___x_2361_, 10, v___x_2360_);
lean_ctor_set(v___x_2361_, 11, v___x_2358_);
lean_ctor_set_uint8(v___x_2361_, sizeof(void*)*12, v___x_2353_);
v___x_2362_ = lean_st_mk_ref(v___x_2361_);
lean_inc(v___y_2349_);
lean_inc_ref(v___y_2348_);
lean_inc(v___y_2347_);
lean_inc_ref(v___y_2346_);
lean_inc(v___x_2362_);
v___x_2363_ = lean_apply_7(v_x_2337_, v___x_2357_, v___x_2362_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, lean_box(0));
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2372_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2366_ = v___x_2363_;
v_isShared_2367_ = v_isSharedCheck_2372_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2363_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2372_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; lean_object* v___x_2370_; 
v___x_2368_ = lean_st_ref_get(v___x_2362_);
lean_dec(v___x_2362_);
lean_dec(v___x_2368_);
if (v_isShared_2367_ == 0)
{
v___x_2370_ = v___x_2366_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2364_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
else
{
lean_dec(v___x_2362_);
return v___x_2363_;
}
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2384_; 
lean_dec_ref(v_snd_2345_);
lean_dec_ref(v_fst_2344_);
lean_dec_ref(v_x_2337_);
v_a_2373_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2375_ = v___x_2354_;
v_isShared_2376_ = v_isSharedCheck_2384_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2354_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2384_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2382_; 
v___x_2377_ = lean_io_error_to_string(v_a_2373_);
v___x_2378_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
v___x_2379_ = l_Lean_MessageData_ofFormat(v___x_2378_);
lean_inc(v_ref_2350_);
v___x_2380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2380_, 0, v_ref_2350_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 0, v___x_2380_);
v___x_2382_ = v___x_2375_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v___x_2380_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_SymM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2337_ = stack[0].m_obj;
lean_object* v_a_2338_ = stack[1].m_obj;
lean_object* v_a_2339_ = stack[2].m_obj;
lean_object* v_a_2340_ = stack[3].m_obj;
lean_object* v_a_2341_ = stack[4].m_obj;
lean_object* v_res_2406_;
v_res_2406_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
stack->m_obj
 = v_res_2406_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg___boxed(lean_object* v_x_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
lean_dec(v_a_2409_);
lean_dec_ref(v_a_2408_);
return v_res_2413_;
}
}
lean_object* l_Lean_Meta_Sym_SymM_run(lean_object* v_00_u03b1_2414_, lean_object* v_x_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
return v___x_2421_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_SymM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2415_ = stack[1].m_obj;
lean_object* v_a_2416_ = stack[2].m_obj;
lean_object* v_a_2417_ = stack[3].m_obj;
lean_object* v_a_2418_ = stack[4].m_obj;
lean_object* v_a_2419_ = stack[5].m_obj;
lean_object* v_res_2422_;
v_res_2422_ = l_Lean_Meta_Sym_SymM_run(lean_box(0), v_x_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
stack->m_obj
 = v_res_2422_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___boxed(lean_object* v_00_u03b1_2423_, lean_object* v_x_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Lean_Meta_Sym_SymM_run(v_00_u03b1_2423_, v_x_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
lean_dec(v_a_2428_);
lean_dec_ref(v_a_2427_);
lean_dec(v_a_2426_);
lean_dec_ref(v_a_2425_);
return v_res_2430_;
}
}
lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg(lean_object* v_a_2431_){
_start:
{
lean_object* v_sharedExprs_2433_; lean_object* v___x_2434_; 
v_sharedExprs_2433_ = lean_ctor_get(v_a_2431_, 0);
lean_inc_ref(v_sharedExprs_2433_);
v___x_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2434_, 0, v_sharedExprs_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getSharedExprs___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2431_ = stack[0].m_obj;
lean_object* v_res_2435_;
v_res_2435_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2431_);
stack->m_obj
 = v_res_2435_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg___boxed(lean_object* v_a_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2436_);
lean_dec_ref(v_a_2436_);
return v_res_2438_;
}
}
lean_object* l_Lean_Meta_Sym_getSharedExprs(lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2439_);
return v___x_2446_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getSharedExprs_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2439_ = stack[0].m_obj;
lean_object* v_a_2440_ = stack[1].m_obj;
lean_object* v_a_2441_ = stack[2].m_obj;
lean_object* v_a_2442_ = stack[3].m_obj;
lean_object* v_a_2443_ = stack[4].m_obj;
lean_object* v_a_2444_ = stack[5].m_obj;
lean_object* v_res_2447_;
v_res_2447_ = l_Lean_Meta_Sym_getSharedExprs(v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
stack->m_obj
 = v_res_2447_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___boxed(lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_Lean_Meta_Sym_getSharedExprs(v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
lean_dec(v_a_2449_);
lean_dec_ref(v_a_2448_);
return v_res_2455_;
}
}
lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object* v_a_2456_){
_start:
{
lean_object* v___x_2458_; lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2467_; 
v___x_2458_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2456_);
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2461_ = v___x_2458_;
v_isShared_2462_ = v_isSharedCheck_2467_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2467_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v_trueExpr_2463_; lean_object* v___x_2465_; 
v_trueExpr_2463_ = lean_ctor_get(v_a_2459_, 0);
lean_inc_ref(v_trueExpr_2463_);
lean_dec(v_a_2459_);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v_trueExpr_2463_);
v___x_2465_ = v___x_2461_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_trueExpr_2463_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getTrueExpr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2456_ = stack[0].m_obj;
lean_object* v_res_2468_;
v_res_2468_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2456_);
stack->m_obj
 = v_res_2468_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg___boxed(lean_object* v_a_2469_, lean_object* v_a_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2469_);
lean_dec_ref(v_a_2469_);
return v_res_2471_;
}
}
lean_object* l_Lean_Meta_Sym_getTrueExpr(lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2472_);
return v___x_2479_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getTrueExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2472_ = stack[0].m_obj;
lean_object* v_a_2473_ = stack[1].m_obj;
lean_object* v_a_2474_ = stack[2].m_obj;
lean_object* v_a_2475_ = stack[3].m_obj;
lean_object* v_a_2476_ = stack[4].m_obj;
lean_object* v_a_2477_ = stack[5].m_obj;
lean_object* v_res_2480_;
v_res_2480_ = l_Lean_Meta_Sym_getTrueExpr(v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_);
stack->m_obj
 = v_res_2480_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___boxed(lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_Meta_Sym_getTrueExpr(v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_);
lean_dec(v_a_2486_);
lean_dec_ref(v_a_2485_);
lean_dec(v_a_2484_);
lean_dec_ref(v_a_2483_);
lean_dec(v_a_2482_);
lean_dec_ref(v_a_2481_);
return v_res_2488_;
}
}
lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object* v_e_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2490_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2504_; 
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2495_ = v___x_2492_;
v_isShared_2496_ = v_isSharedCheck_2504_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2492_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2504_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
size_t v___x_2497_; size_t v___x_2498_; uint8_t v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2502_; 
v___x_2497_ = lean_ptr_addr(v_e_2489_);
v___x_2498_ = lean_ptr_addr(v_a_2493_);
lean_dec(v_a_2493_);
v___x_2499_ = lean_usize_dec_eq(v___x_2497_, v___x_2498_);
v___x_2500_ = lean_box(v___x_2499_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 0, v___x_2500_);
v___x_2502_ = v___x_2495_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2500_);
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
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
v_a_2505_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2492_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2492_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_isTrueExpr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2489_ = stack[0].m_obj;
lean_object* v_a_2490_ = stack[1].m_obj;
lean_object* v_res_2513_;
v_res_2513_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_2489_, v_a_2490_);
stack->m_obj
 = v_res_2513_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg___boxed(lean_object* v_e_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_2514_, v_a_2515_);
lean_dec_ref(v_a_2515_);
lean_dec_ref(v_e_2514_);
return v_res_2517_;
}
}
lean_object* l_Lean_Meta_Sym_isTrueExpr(lean_object* v_e_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_2518_, v_a_2519_);
return v___x_2526_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_isTrueExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2518_ = stack[0].m_obj;
lean_object* v_a_2519_ = stack[1].m_obj;
lean_object* v_a_2520_ = stack[2].m_obj;
lean_object* v_a_2521_ = stack[3].m_obj;
lean_object* v_a_2522_ = stack[4].m_obj;
lean_object* v_a_2523_ = stack[5].m_obj;
lean_object* v_a_2524_ = stack[6].m_obj;
lean_object* v_res_2527_;
v_res_2527_ = l_Lean_Meta_Sym_isTrueExpr(v_e_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
stack->m_obj
 = v_res_2527_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___boxed(lean_object* v_e_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Lean_Meta_Sym_isTrueExpr(v_e_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
lean_dec(v_a_2534_);
lean_dec_ref(v_a_2533_);
lean_dec(v_a_2532_);
lean_dec_ref(v_a_2531_);
lean_dec(v_a_2530_);
lean_dec_ref(v_a_2529_);
lean_dec_ref(v_e_2528_);
return v_res_2536_;
}
}
lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object* v_a_2537_){
_start:
{
lean_object* v___x_2539_; lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2548_; 
v___x_2539_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2537_);
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2542_ = v___x_2539_;
v_isShared_2543_ = v_isSharedCheck_2548_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2539_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2548_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v_falseExpr_2544_; lean_object* v___x_2546_; 
v_falseExpr_2544_ = lean_ctor_get(v_a_2540_, 1);
lean_inc_ref(v_falseExpr_2544_);
lean_dec(v_a_2540_);
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 0, v_falseExpr_2544_);
v___x_2546_ = v___x_2542_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_falseExpr_2544_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getFalseExpr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2537_ = stack[0].m_obj;
lean_object* v_res_2549_;
v_res_2549_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2537_);
stack->m_obj
 = v_res_2549_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg___boxed(lean_object* v_a_2550_, lean_object* v_a_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2550_);
lean_dec_ref(v_a_2550_);
return v_res_2552_;
}
}
lean_object* l_Lean_Meta_Sym_getFalseExpr(lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2553_);
return v___x_2560_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getFalseExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2553_ = stack[0].m_obj;
lean_object* v_a_2554_ = stack[1].m_obj;
lean_object* v_a_2555_ = stack[2].m_obj;
lean_object* v_a_2556_ = stack[3].m_obj;
lean_object* v_a_2557_ = stack[4].m_obj;
lean_object* v_a_2558_ = stack[5].m_obj;
lean_object* v_res_2561_;
v_res_2561_ = l_Lean_Meta_Sym_getFalseExpr(v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_);
stack->m_obj
 = v_res_2561_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___boxed(lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_Lean_Meta_Sym_getFalseExpr(v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
lean_dec(v_a_2565_);
lean_dec_ref(v_a_2564_);
lean_dec(v_a_2563_);
lean_dec_ref(v_a_2562_);
return v_res_2569_;
}
}
lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object* v_e_2570_, lean_object* v_a_2571_){
_start:
{
lean_object* v___x_2573_; 
v___x_2573_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2571_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2585_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2576_ = v___x_2573_;
v_isShared_2577_ = v_isSharedCheck_2585_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2573_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2585_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
size_t v___x_2578_; size_t v___x_2579_; uint8_t v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2583_; 
v___x_2578_ = lean_ptr_addr(v_e_2570_);
v___x_2579_ = lean_ptr_addr(v_a_2574_);
lean_dec(v_a_2574_);
v___x_2580_ = lean_usize_dec_eq(v___x_2578_, v___x_2579_);
v___x_2581_ = lean_box(v___x_2580_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v___x_2581_);
v___x_2583_ = v___x_2576_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
v_a_2586_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2573_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2573_);
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
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_isFalseExpr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2570_ = stack[0].m_obj;
lean_object* v_a_2571_ = stack[1].m_obj;
lean_object* v_res_2594_;
v_res_2594_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_2570_, v_a_2571_);
stack->m_obj
 = v_res_2594_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg___boxed(lean_object* v_e_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_){
_start:
{
lean_object* v_res_2598_; 
v_res_2598_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_2595_, v_a_2596_);
lean_dec_ref(v_a_2596_);
lean_dec_ref(v_e_2595_);
return v_res_2598_;
}
}
lean_object* l_Lean_Meta_Sym_isFalseExpr(lean_object* v_e_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_2599_, v_a_2600_);
return v___x_2607_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_isFalseExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2599_ = stack[0].m_obj;
lean_object* v_a_2600_ = stack[1].m_obj;
lean_object* v_a_2601_ = stack[2].m_obj;
lean_object* v_a_2602_ = stack[3].m_obj;
lean_object* v_a_2603_ = stack[4].m_obj;
lean_object* v_a_2604_ = stack[5].m_obj;
lean_object* v_a_2605_ = stack[6].m_obj;
lean_object* v_res_2608_;
v_res_2608_ = l_Lean_Meta_Sym_isFalseExpr(v_e_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_);
stack->m_obj
 = v_res_2608_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___boxed(lean_object* v_e_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_Lean_Meta_Sym_isFalseExpr(v_e_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_);
lean_dec(v_a_2615_);
lean_dec_ref(v_a_2614_);
lean_dec(v_a_2613_);
lean_dec_ref(v_a_2612_);
lean_dec(v_a_2611_);
lean_dec_ref(v_a_2610_);
lean_dec_ref(v_e_2609_);
return v_res_2617_;
}
}
lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object* v_a_2618_){
_start:
{
lean_object* v___x_2620_; lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2629_; 
v___x_2620_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2618_);
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2623_ = v___x_2620_;
v_isShared_2624_ = v_isSharedCheck_2629_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2620_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2629_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v_btrueExpr_2625_; lean_object* v___x_2627_; 
v_btrueExpr_2625_ = lean_ctor_get(v_a_2621_, 3);
lean_inc_ref(v_btrueExpr_2625_);
lean_dec(v_a_2621_);
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 0, v_btrueExpr_2625_);
v___x_2627_ = v___x_2623_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_btrueExpr_2625_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getBoolTrueExpr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2618_ = stack[0].m_obj;
lean_object* v_res_2630_;
v_res_2630_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2618_);
stack->m_obj
 = v_res_2630_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg___boxed(lean_object* v_a_2631_, lean_object* v_a_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2631_);
lean_dec_ref(v_a_2631_);
return v_res_2633_;
}
}
lean_object* l_Lean_Meta_Sym_getBoolTrueExpr(lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2634_);
return v___x_2641_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getBoolTrueExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2634_ = stack[0].m_obj;
lean_object* v_a_2635_ = stack[1].m_obj;
lean_object* v_a_2636_ = stack[2].m_obj;
lean_object* v_a_2637_ = stack[3].m_obj;
lean_object* v_a_2638_ = stack[4].m_obj;
lean_object* v_a_2639_ = stack[5].m_obj;
lean_object* v_res_2642_;
v_res_2642_ = l_Lean_Meta_Sym_getBoolTrueExpr(v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_);
stack->m_obj
 = v_res_2642_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___boxed(lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l_Lean_Meta_Sym_getBoolTrueExpr(v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_);
lean_dec(v_a_2648_);
lean_dec_ref(v_a_2647_);
lean_dec(v_a_2646_);
lean_dec_ref(v_a_2645_);
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2643_);
return v_res_2650_;
}
}
lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg(lean_object* v_e_2651_, lean_object* v_a_2652_){
_start:
{
lean_object* v___x_2654_; 
v___x_2654_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2652_);
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
LEAN_EXPORT void l_Lean_Meta_Sym_isBoolTrueExpr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2651_ = stack[0].m_obj;
lean_object* v_a_2652_ = stack[1].m_obj;
lean_object* v_res_2675_;
v_res_2675_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_2651_, v_a_2652_);
stack->m_obj
 = v_res_2675_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg___boxed(lean_object* v_e_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_2676_, v_a_2677_);
lean_dec_ref(v_a_2677_);
lean_dec_ref(v_e_2676_);
return v_res_2679_;
}
}
lean_object* l_Lean_Meta_Sym_isBoolTrueExpr(lean_object* v_e_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_){
_start:
{
lean_object* v___x_2688_; 
v___x_2688_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_2680_, v_a_2681_);
return v___x_2688_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_isBoolTrueExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2680_ = stack[0].m_obj;
lean_object* v_a_2681_ = stack[1].m_obj;
lean_object* v_a_2682_ = stack[2].m_obj;
lean_object* v_a_2683_ = stack[3].m_obj;
lean_object* v_a_2684_ = stack[4].m_obj;
lean_object* v_a_2685_ = stack[5].m_obj;
lean_object* v_a_2686_ = stack[6].m_obj;
lean_object* v_res_2689_;
v_res_2689_ = l_Lean_Meta_Sym_isBoolTrueExpr(v_e_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
stack->m_obj
 = v_res_2689_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___boxed(lean_object* v_e_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l_Lean_Meta_Sym_isBoolTrueExpr(v_e_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
lean_dec(v_a_2696_);
lean_dec_ref(v_a_2695_);
lean_dec(v_a_2694_);
lean_dec_ref(v_a_2693_);
lean_dec(v_a_2692_);
lean_dec_ref(v_a_2691_);
lean_dec_ref(v_e_2690_);
return v_res_2698_;
}
}
lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object* v_a_2699_){
_start:
{
lean_object* v___x_2701_; lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2710_; 
v___x_2701_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2699_);
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2704_ = v___x_2701_;
v_isShared_2705_ = v_isSharedCheck_2710_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2701_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2710_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v_bfalseExpr_2706_; lean_object* v___x_2708_; 
v_bfalseExpr_2706_ = lean_ctor_get(v_a_2702_, 4);
lean_inc_ref(v_bfalseExpr_2706_);
lean_dec(v_a_2702_);
if (v_isShared_2705_ == 0)
{
lean_ctor_set(v___x_2704_, 0, v_bfalseExpr_2706_);
v___x_2708_ = v___x_2704_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_bfalseExpr_2706_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getBoolFalseExpr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2699_ = stack[0].m_obj;
lean_object* v_res_2711_;
v_res_2711_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2699_);
stack->m_obj
 = v_res_2711_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg___boxed(lean_object* v_a_2712_, lean_object* v_a_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2712_);
lean_dec_ref(v_a_2712_);
return v_res_2714_;
}
}
lean_object* l_Lean_Meta_Sym_getBoolFalseExpr(lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2715_);
return v___x_2722_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getBoolFalseExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2715_ = stack[0].m_obj;
lean_object* v_a_2716_ = stack[1].m_obj;
lean_object* v_a_2717_ = stack[2].m_obj;
lean_object* v_a_2718_ = stack[3].m_obj;
lean_object* v_a_2719_ = stack[4].m_obj;
lean_object* v_a_2720_ = stack[5].m_obj;
lean_object* v_res_2723_;
v_res_2723_ = l_Lean_Meta_Sym_getBoolFalseExpr(v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_);
stack->m_obj
 = v_res_2723_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___boxed(lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_Lean_Meta_Sym_getBoolFalseExpr(v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_);
lean_dec(v_a_2729_);
lean_dec_ref(v_a_2728_);
lean_dec(v_a_2727_);
lean_dec_ref(v_a_2726_);
lean_dec(v_a_2725_);
lean_dec_ref(v_a_2724_);
return v_res_2731_;
}
}
lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg(lean_object* v_e_2732_, lean_object* v_a_2733_){
_start:
{
lean_object* v___x_2735_; 
v___x_2735_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2733_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2747_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2738_ = v___x_2735_;
v_isShared_2739_ = v_isSharedCheck_2747_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2735_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2747_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
size_t v___x_2740_; size_t v___x_2741_; uint8_t v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2745_; 
v___x_2740_ = lean_ptr_addr(v_e_2732_);
v___x_2741_ = lean_ptr_addr(v_a_2736_);
lean_dec(v_a_2736_);
v___x_2742_ = lean_usize_dec_eq(v___x_2740_, v___x_2741_);
v___x_2743_ = lean_box(v___x_2742_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 0, v___x_2743_);
v___x_2745_ = v___x_2738_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2743_);
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
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
v_a_2748_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2750_ = v___x_2735_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2735_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2748_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_isBoolFalseExpr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2732_ = stack[0].m_obj;
lean_object* v_a_2733_ = stack[1].m_obj;
lean_object* v_res_2756_;
v_res_2756_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_2732_, v_a_2733_);
stack->m_obj
 = v_res_2756_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg___boxed(lean_object* v_e_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_2757_, v_a_2758_);
lean_dec_ref(v_a_2758_);
lean_dec_ref(v_e_2757_);
return v_res_2760_;
}
}
lean_object* l_Lean_Meta_Sym_isBoolFalseExpr(lean_object* v_e_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_){
_start:
{
lean_object* v___x_2769_; 
v___x_2769_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_2761_, v_a_2762_);
return v___x_2769_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_isBoolFalseExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2761_ = stack[0].m_obj;
lean_object* v_a_2762_ = stack[1].m_obj;
lean_object* v_a_2763_ = stack[2].m_obj;
lean_object* v_a_2764_ = stack[3].m_obj;
lean_object* v_a_2765_ = stack[4].m_obj;
lean_object* v_a_2766_ = stack[5].m_obj;
lean_object* v_a_2767_ = stack[6].m_obj;
lean_object* v_res_2770_;
v_res_2770_ = l_Lean_Meta_Sym_isBoolFalseExpr(v_e_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_);
stack->m_obj
 = v_res_2770_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___boxed(lean_object* v_e_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Lean_Meta_Sym_isBoolFalseExpr(v_e_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
lean_dec(v_a_2777_);
lean_dec_ref(v_a_2776_);
lean_dec(v_a_2775_);
lean_dec_ref(v_a_2774_);
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
lean_dec_ref(v_e_2771_);
return v_res_2779_;
}
}
lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg(lean_object* v_a_2780_){
_start:
{
lean_object* v___x_2782_; lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2791_; 
v___x_2782_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2780_);
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2785_ = v___x_2782_;
v_isShared_2786_ = v_isSharedCheck_2791_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2782_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2791_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v_natZExpr_2787_; lean_object* v___x_2789_; 
v_natZExpr_2787_ = lean_ctor_get(v_a_2783_, 2);
lean_inc_ref(v_natZExpr_2787_);
lean_dec(v_a_2783_);
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 0, v_natZExpr_2787_);
v___x_2789_ = v___x_2785_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_natZExpr_2787_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getNatZeroExpr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2780_ = stack[0].m_obj;
lean_object* v_res_2792_;
v_res_2792_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_2780_);
stack->m_obj
 = v_res_2792_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg___boxed(lean_object* v_a_2793_, lean_object* v_a_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_2793_);
lean_dec_ref(v_a_2793_);
return v_res_2795_;
}
}
lean_object* l_Lean_Meta_Sym_getNatZeroExpr(lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v___x_2803_; 
v___x_2803_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_2796_);
return v___x_2803_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getNatZeroExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2796_ = stack[0].m_obj;
lean_object* v_a_2797_ = stack[1].m_obj;
lean_object* v_a_2798_ = stack[2].m_obj;
lean_object* v_a_2799_ = stack[3].m_obj;
lean_object* v_a_2800_ = stack[4].m_obj;
lean_object* v_a_2801_ = stack[5].m_obj;
lean_object* v_res_2804_;
v_res_2804_ = l_Lean_Meta_Sym_getNatZeroExpr(v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_);
stack->m_obj
 = v_res_2804_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___boxed(lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l_Lean_Meta_Sym_getNatZeroExpr(v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_);
lean_dec(v_a_2810_);
lean_dec_ref(v_a_2809_);
lean_dec(v_a_2808_);
lean_dec_ref(v_a_2807_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
return v_res_2812_;
}
}
lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg(lean_object* v_a_2813_){
_start:
{
lean_object* v___x_2815_; lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2824_; 
v___x_2815_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2813_);
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2818_ = v___x_2815_;
v_isShared_2819_ = v_isSharedCheck_2824_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2815_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2824_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v_ordEqExpr_2820_; lean_object* v___x_2822_; 
v_ordEqExpr_2820_ = lean_ctor_get(v_a_2816_, 5);
lean_inc_ref(v_ordEqExpr_2820_);
lean_dec(v_a_2816_);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v_ordEqExpr_2820_);
v___x_2822_ = v___x_2818_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_ordEqExpr_2820_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getOrderingEqExpr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2813_ = stack[0].m_obj;
lean_object* v_res_2825_;
v_res_2825_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_2813_);
stack->m_obj
 = v_res_2825_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg___boxed(lean_object* v_a_2826_, lean_object* v_a_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_2826_);
lean_dec_ref(v_a_2826_);
return v_res_2828_;
}
}
lean_object* l_Lean_Meta_Sym_getOrderingEqExpr(lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_2829_);
return v___x_2836_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getOrderingEqExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2829_ = stack[0].m_obj;
lean_object* v_a_2830_ = stack[1].m_obj;
lean_object* v_a_2831_ = stack[2].m_obj;
lean_object* v_a_2832_ = stack[3].m_obj;
lean_object* v_a_2833_ = stack[4].m_obj;
lean_object* v_a_2834_ = stack[5].m_obj;
lean_object* v_res_2837_;
v_res_2837_ = l_Lean_Meta_Sym_getOrderingEqExpr(v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_);
stack->m_obj
 = v_res_2837_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___boxed(lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l_Lean_Meta_Sym_getOrderingEqExpr(v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_);
lean_dec(v_a_2843_);
lean_dec_ref(v_a_2842_);
lean_dec(v_a_2841_);
lean_dec_ref(v_a_2840_);
lean_dec(v_a_2839_);
lean_dec_ref(v_a_2838_);
return v_res_2845_;
}
}
lean_object* l_Lean_Meta_Sym_getIntExpr___redArg(lean_object* v_a_2846_){
_start:
{
lean_object* v___x_2848_; lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2857_; 
v___x_2848_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_2846_);
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2851_ = v___x_2848_;
v_isShared_2852_ = v_isSharedCheck_2857_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2848_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2857_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v_intExpr_2853_; lean_object* v___x_2855_; 
v_intExpr_2853_ = lean_ctor_get(v_a_2849_, 6);
lean_inc_ref(v_intExpr_2853_);
lean_dec(v_a_2849_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 0, v_intExpr_2853_);
v___x_2855_ = v___x_2851_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_intExpr_2853_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getIntExpr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2846_ = stack[0].m_obj;
lean_object* v_res_2858_;
v_res_2858_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_2846_);
stack->m_obj
 = v_res_2858_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg___boxed(lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_2859_);
lean_dec_ref(v_a_2859_);
return v_res_2861_;
}
}
lean_object* l_Lean_Meta_Sym_getIntExpr(lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_){
_start:
{
lean_object* v___x_2869_; 
v___x_2869_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_2862_);
return v___x_2869_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getIntExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2862_ = stack[0].m_obj;
lean_object* v_a_2863_ = stack[1].m_obj;
lean_object* v_a_2864_ = stack[2].m_obj;
lean_object* v_a_2865_ = stack[3].m_obj;
lean_object* v_a_2866_ = stack[4].m_obj;
lean_object* v_a_2867_ = stack[5].m_obj;
lean_object* v_res_2870_;
v_res_2870_ = l_Lean_Meta_Sym_getIntExpr(v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_);
stack->m_obj
 = v_res_2870_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___boxed(lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Lean_Meta_Sym_getIntExpr(v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_);
lean_dec(v_a_2876_);
lean_dec_ref(v_a_2875_);
lean_dec(v_a_2874_);
lean_dec_ref(v_a_2873_);
lean_dec(v_a_2872_);
lean_dec_ref(v_a_2871_);
return v_res_2878_;
}
}
lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg(lean_object* v_k_2879_, lean_object* v_ctx_2880_, lean_object* v_a_2881_){
_start:
{
lean_object* v___x_2883_; lean_object* v_share_2884_; lean_object* v_maxFVar_2885_; lean_object* v_proofInstInfo_2886_; lean_object* v_proofInstInfoFVar_2887_; lean_object* v_inferType_2888_; lean_object* v_getLevel_2889_; lean_object* v_congrInfo_2890_; lean_object* v_defEqI_2891_; lean_object* v_extensions_2892_; lean_object* v_issues_2893_; lean_object* v_canon_2894_; lean_object* v_instanceOverrides_2895_; uint8_t v_debug_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2958_; 
v___x_2883_ = lean_st_ref_take(v_a_2881_);
v_share_2884_ = lean_ctor_get(v___x_2883_, 0);
v_maxFVar_2885_ = lean_ctor_get(v___x_2883_, 1);
v_proofInstInfo_2886_ = lean_ctor_get(v___x_2883_, 2);
v_proofInstInfoFVar_2887_ = lean_ctor_get(v___x_2883_, 3);
v_inferType_2888_ = lean_ctor_get(v___x_2883_, 4);
v_getLevel_2889_ = lean_ctor_get(v___x_2883_, 5);
v_congrInfo_2890_ = lean_ctor_get(v___x_2883_, 6);
v_defEqI_2891_ = lean_ctor_get(v___x_2883_, 7);
v_extensions_2892_ = lean_ctor_get(v___x_2883_, 8);
v_issues_2893_ = lean_ctor_get(v___x_2883_, 9);
v_canon_2894_ = lean_ctor_get(v___x_2883_, 10);
v_instanceOverrides_2895_ = lean_ctor_get(v___x_2883_, 11);
v_debug_2896_ = lean_ctor_get_uint8(v___x_2883_, sizeof(void*)*12);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2898_ = v___x_2883_;
v_isShared_2899_ = v_isSharedCheck_2958_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_instanceOverrides_2895_);
lean_inc(v_canon_2894_);
lean_inc(v_issues_2893_);
lean_inc(v_extensions_2892_);
lean_inc(v_defEqI_2891_);
lean_inc(v_congrInfo_2890_);
lean_inc(v_getLevel_2889_);
lean_inc(v_inferType_2888_);
lean_inc(v_proofInstInfoFVar_2887_);
lean_inc(v_proofInstInfo_2886_);
lean_inc(v_maxFVar_2885_);
lean_inc(v_share_2884_);
lean_dec(v___x_2883_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2958_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2900_; lean_object* v___x_2902_; 
v___x_2900_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__1___closed__0);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_2900_);
v___x_2902_ = v___x_2898_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2900_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v_maxFVar_2885_);
lean_ctor_set(v_reuseFailAlloc_2957_, 2, v_proofInstInfo_2886_);
lean_ctor_set(v_reuseFailAlloc_2957_, 3, v_proofInstInfoFVar_2887_);
lean_ctor_set(v_reuseFailAlloc_2957_, 4, v_inferType_2888_);
lean_ctor_set(v_reuseFailAlloc_2957_, 5, v_getLevel_2889_);
lean_ctor_set(v_reuseFailAlloc_2957_, 6, v_congrInfo_2890_);
lean_ctor_set(v_reuseFailAlloc_2957_, 7, v_defEqI_2891_);
lean_ctor_set(v_reuseFailAlloc_2957_, 8, v_extensions_2892_);
lean_ctor_set(v_reuseFailAlloc_2957_, 9, v_issues_2893_);
lean_ctor_set(v_reuseFailAlloc_2957_, 10, v_canon_2894_);
lean_ctor_set(v_reuseFailAlloc_2957_, 11, v_instanceOverrides_2895_);
lean_ctor_set_uint8(v_reuseFailAlloc_2957_, sizeof(void*)*12, v_debug_2896_);
v___x_2902_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = lean_st_ref_put(v_a_2881_, v___x_2902_);
v___x_2904_ = lean_apply_2(v_k_2879_, v_ctx_2880_, v_share_2884_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; lean_object* v_a_2906_; lean_object* v___x_2907_; lean_object* v_maxFVar_2908_; lean_object* v_proofInstInfo_2909_; lean_object* v_proofInstInfoFVar_2910_; lean_object* v_inferType_2911_; lean_object* v_getLevel_2912_; lean_object* v_congrInfo_2913_; lean_object* v_defEqI_2914_; lean_object* v_extensions_2915_; lean_object* v_issues_2916_; lean_object* v_canon_2917_; lean_object* v_instanceOverrides_2918_; uint8_t v_debug_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2929_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_a_2905_);
v_a_2906_ = lean_ctor_get(v___x_2904_, 1);
lean_inc(v_a_2906_);
lean_dec_ref_known(v___x_2904_, 2);
v___x_2907_ = lean_st_ref_take(v_a_2881_);
v_maxFVar_2908_ = lean_ctor_get(v___x_2907_, 1);
v_proofInstInfo_2909_ = lean_ctor_get(v___x_2907_, 2);
v_proofInstInfoFVar_2910_ = lean_ctor_get(v___x_2907_, 3);
v_inferType_2911_ = lean_ctor_get(v___x_2907_, 4);
v_getLevel_2912_ = lean_ctor_get(v___x_2907_, 5);
v_congrInfo_2913_ = lean_ctor_get(v___x_2907_, 6);
v_defEqI_2914_ = lean_ctor_get(v___x_2907_, 7);
v_extensions_2915_ = lean_ctor_get(v___x_2907_, 8);
v_issues_2916_ = lean_ctor_get(v___x_2907_, 9);
v_canon_2917_ = lean_ctor_get(v___x_2907_, 10);
v_instanceOverrides_2918_ = lean_ctor_get(v___x_2907_, 11);
v_debug_2919_ = lean_ctor_get_uint8(v___x_2907_, sizeof(void*)*12);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2929_ == 0)
{
lean_object* v_unused_2930_; 
v_unused_2930_ = lean_ctor_get(v___x_2907_, 0);
lean_dec(v_unused_2930_);
v___x_2921_ = v___x_2907_;
v_isShared_2922_ = v_isSharedCheck_2929_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_instanceOverrides_2918_);
lean_inc(v_canon_2917_);
lean_inc(v_issues_2916_);
lean_inc(v_extensions_2915_);
lean_inc(v_defEqI_2914_);
lean_inc(v_congrInfo_2913_);
lean_inc(v_getLevel_2912_);
lean_inc(v_inferType_2911_);
lean_inc(v_proofInstInfoFVar_2910_);
lean_inc(v_proofInstInfo_2909_);
lean_inc(v_maxFVar_2908_);
lean_dec(v___x_2907_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2929_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
lean_ctor_set(v___x_2921_, 0, v_a_2906_);
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2906_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v_maxFVar_2908_);
lean_ctor_set(v_reuseFailAlloc_2928_, 2, v_proofInstInfo_2909_);
lean_ctor_set(v_reuseFailAlloc_2928_, 3, v_proofInstInfoFVar_2910_);
lean_ctor_set(v_reuseFailAlloc_2928_, 4, v_inferType_2911_);
lean_ctor_set(v_reuseFailAlloc_2928_, 5, v_getLevel_2912_);
lean_ctor_set(v_reuseFailAlloc_2928_, 6, v_congrInfo_2913_);
lean_ctor_set(v_reuseFailAlloc_2928_, 7, v_defEqI_2914_);
lean_ctor_set(v_reuseFailAlloc_2928_, 8, v_extensions_2915_);
lean_ctor_set(v_reuseFailAlloc_2928_, 9, v_issues_2916_);
lean_ctor_set(v_reuseFailAlloc_2928_, 10, v_canon_2917_);
lean_ctor_set(v_reuseFailAlloc_2928_, 11, v_instanceOverrides_2918_);
lean_ctor_set_uint8(v_reuseFailAlloc_2928_, sizeof(void*)*12, v_debug_2919_);
v___x_2924_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2925_ = lean_st_ref_put(v_a_2881_, v___x_2924_);
v___x_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2926_, 0, v_a_2905_);
v___x_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
return v___x_2927_;
}
}
}
else
{
lean_object* v_a_2931_; lean_object* v_a_2932_; lean_object* v___x_2933_; lean_object* v_maxFVar_2934_; lean_object* v_proofInstInfo_2935_; lean_object* v_proofInstInfoFVar_2936_; lean_object* v_inferType_2937_; lean_object* v_getLevel_2938_; lean_object* v_congrInfo_2939_; lean_object* v_defEqI_2940_; lean_object* v_extensions_2941_; lean_object* v_issues_2942_; lean_object* v_canon_2943_; lean_object* v_instanceOverrides_2944_; uint8_t v_debug_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2955_; 
v_a_2931_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_a_2931_);
v_a_2932_ = lean_ctor_get(v___x_2904_, 1);
lean_inc(v_a_2932_);
lean_dec_ref_known(v___x_2904_, 2);
v___x_2933_ = lean_st_ref_take(v_a_2881_);
v_maxFVar_2934_ = lean_ctor_get(v___x_2933_, 1);
v_proofInstInfo_2935_ = lean_ctor_get(v___x_2933_, 2);
v_proofInstInfoFVar_2936_ = lean_ctor_get(v___x_2933_, 3);
v_inferType_2937_ = lean_ctor_get(v___x_2933_, 4);
v_getLevel_2938_ = lean_ctor_get(v___x_2933_, 5);
v_congrInfo_2939_ = lean_ctor_get(v___x_2933_, 6);
v_defEqI_2940_ = lean_ctor_get(v___x_2933_, 7);
v_extensions_2941_ = lean_ctor_get(v___x_2933_, 8);
v_issues_2942_ = lean_ctor_get(v___x_2933_, 9);
v_canon_2943_ = lean_ctor_get(v___x_2933_, 10);
v_instanceOverrides_2944_ = lean_ctor_get(v___x_2933_, 11);
v_debug_2945_ = lean_ctor_get_uint8(v___x_2933_, sizeof(void*)*12);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2955_ == 0)
{
lean_object* v_unused_2956_; 
v_unused_2956_ = lean_ctor_get(v___x_2933_, 0);
lean_dec(v_unused_2956_);
v___x_2947_ = v___x_2933_;
v_isShared_2948_ = v_isSharedCheck_2955_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_instanceOverrides_2944_);
lean_inc(v_canon_2943_);
lean_inc(v_issues_2942_);
lean_inc(v_extensions_2941_);
lean_inc(v_defEqI_2940_);
lean_inc(v_congrInfo_2939_);
lean_inc(v_getLevel_2938_);
lean_inc(v_inferType_2937_);
lean_inc(v_proofInstInfoFVar_2936_);
lean_inc(v_proofInstInfo_2935_);
lean_inc(v_maxFVar_2934_);
lean_dec(v___x_2933_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2955_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 0, v_a_2932_);
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2932_);
lean_ctor_set(v_reuseFailAlloc_2954_, 1, v_maxFVar_2934_);
lean_ctor_set(v_reuseFailAlloc_2954_, 2, v_proofInstInfo_2935_);
lean_ctor_set(v_reuseFailAlloc_2954_, 3, v_proofInstInfoFVar_2936_);
lean_ctor_set(v_reuseFailAlloc_2954_, 4, v_inferType_2937_);
lean_ctor_set(v_reuseFailAlloc_2954_, 5, v_getLevel_2938_);
lean_ctor_set(v_reuseFailAlloc_2954_, 6, v_congrInfo_2939_);
lean_ctor_set(v_reuseFailAlloc_2954_, 7, v_defEqI_2940_);
lean_ctor_set(v_reuseFailAlloc_2954_, 8, v_extensions_2941_);
lean_ctor_set(v_reuseFailAlloc_2954_, 9, v_issues_2942_);
lean_ctor_set(v_reuseFailAlloc_2954_, 10, v_canon_2943_);
lean_ctor_set(v_reuseFailAlloc_2954_, 11, v_instanceOverrides_2944_);
lean_ctor_set_uint8(v_reuseFailAlloc_2954_, sizeof(void*)*12, v_debug_2945_);
v___x_2950_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2951_ = lean_st_ref_put(v_a_2881_, v___x_2950_);
v___x_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2952_, 0, v_a_2931_);
v___x_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2952_);
return v___x_2953_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_runShareCommonM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2879_ = stack[0].m_obj;
lean_object* v_ctx_2880_ = stack[1].m_obj;
lean_object* v_a_2881_ = stack[2].m_obj;
lean_object* v_res_2959_;
v_res_2959_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v_k_2879_, v_ctx_2880_, v_a_2881_);
stack->m_obj
 = v_res_2959_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg___boxed(lean_object* v_k_2960_, lean_object* v_ctx_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v_k_2960_, v_ctx_2961_, v_a_2962_);
lean_dec(v_a_2962_);
return v_res_2964_;
}
}
lean_object* l_Lean_Meta_Sym_runShareCommonM(lean_object* v_00_u03b1_2965_, lean_object* v_k_2966_, lean_object* v_ctx_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v_k_2966_, v_ctx_2967_, v_a_2969_);
return v___x_2975_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_runShareCommonM_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2966_ = stack[1].m_obj;
lean_object* v_ctx_2967_ = stack[2].m_obj;
lean_object* v_a_2968_ = stack[3].m_obj;
lean_object* v_a_2969_ = stack[4].m_obj;
lean_object* v_a_2970_ = stack[5].m_obj;
lean_object* v_a_2971_ = stack[6].m_obj;
lean_object* v_a_2972_ = stack[7].m_obj;
lean_object* v_a_2973_ = stack[8].m_obj;
lean_object* v_res_2976_;
v_res_2976_ = l_Lean_Meta_Sym_runShareCommonM(lean_box(0), v_k_2966_, v_ctx_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_);
stack->m_obj
 = v_res_2976_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_runShareCommonM___boxed(lean_object* v_00_u03b1_2977_, lean_object* v_k_2978_, lean_object* v_ctx_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Lean_Meta_Sym_runShareCommonM(v_00_u03b1_2977_, v_k_2978_, v_ctx_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_);
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec_ref(v_a_2982_);
lean_dec(v_a_2981_);
lean_dec_ref(v_a_2980_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___lam__0(lean_object* v_ctx_2988_){
_start:
{
lean_object* v_config_2989_; lean_object* v_sharedExprs_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3007_; 
v_config_2989_ = lean_ctor_get(v_ctx_2988_, 1);
v_sharedExprs_2990_ = lean_ctor_get(v_ctx_2988_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v_ctx_2988_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_2992_ = v_ctx_2988_;
v_isShared_2993_ = v_isSharedCheck_3007_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_config_2989_);
lean_inc(v_sharedExprs_2990_);
lean_dec(v_ctx_2988_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3007_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
uint8_t v_verbose_2994_; uint8_t v_enforceUnfoldReducible_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3006_; 
v_verbose_2994_ = lean_ctor_get_uint8(v_config_2989_, 0);
v_enforceUnfoldReducible_2995_ = lean_ctor_get_uint8(v_config_2989_, 1);
v_isSharedCheck_3006_ = !lean_is_exclusive(v_config_2989_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_2997_ = v_config_2989_;
v_isShared_2998_ = v_isSharedCheck_3006_;
goto v_resetjp_2996_;
}
else
{
lean_dec(v_config_2989_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3006_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
uint8_t v___x_2999_; lean_object* v___x_3001_; 
v___x_2999_ = 0;
if (v_isShared_2998_ == 0)
{
v___x_3001_ = v___x_2997_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3005_, 0, v_verbose_2994_);
lean_ctor_set_uint8(v_reuseFailAlloc_3005_, 1, v_enforceUnfoldReducible_2995_);
v___x_3001_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_object* v___x_3003_; 
lean_ctor_set_uint8(v___x_3001_, 2, v___x_2999_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 1, v___x_3001_);
v___x_3003_ = v___x_2992_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_sharedExprs_2990_);
lean_ctor_set(v_reuseFailAlloc_3004_, 1, v___x_3001_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg(lean_object* v_inst_3009_, lean_object* v_x_3010_){
_start:
{
lean_object* v___f_3011_; lean_object* v___x_3012_; 
v___f_3011_ = ((lean_object*)(l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg___closed__0));
v___x_3012_ = lean_apply_3(v_inst_3009_, lean_box(0), v___f_3011_, v_x_3010_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck(lean_object* v_m_3013_, lean_object* v_00_u03b1_3014_, lean_object* v_inst_3015_, lean_object* v_x_3016_){
_start:
{
lean_object* v___x_3017_; 
v___x_3017_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___redArg(v_inst_3015_, v_x_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___lam__0(lean_object* v_ctx_3018_){
_start:
{
lean_object* v_config_3019_; lean_object* v_sharedExprs_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3036_; 
v_config_3019_ = lean_ctor_get(v_ctx_3018_, 1);
v_sharedExprs_3020_ = lean_ctor_get(v_ctx_3018_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v_ctx_3018_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3022_ = v_ctx_3018_;
v_isShared_3023_ = v_isSharedCheck_3036_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_config_3019_);
lean_inc(v_sharedExprs_3020_);
lean_dec(v_ctx_3018_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3036_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
uint8_t v_verbose_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3035_; 
v_verbose_3024_ = lean_ctor_get_uint8(v_config_3019_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v_config_3019_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3026_ = v_config_3019_;
v_isShared_3027_ = v_isSharedCheck_3035_;
goto v_resetjp_3025_;
}
else
{
lean_dec(v_config_3019_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3035_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
uint8_t v___x_3028_; lean_object* v___x_3030_; 
v___x_3028_ = 0;
if (v_isShared_3027_ == 0)
{
v___x_3030_ = v___x_3026_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3034_, 0, v_verbose_3024_);
v___x_3030_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
lean_object* v___x_3032_; 
lean_ctor_set_uint8(v___x_3030_, 1, v___x_3028_);
lean_ctor_set_uint8(v___x_3030_, 2, v___x_3028_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 1, v___x_3030_);
v___x_3032_ = v___x_3022_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_sharedExprs_3020_);
lean_ctor_set(v_reuseFailAlloc_3033_, 1, v___x_3030_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___redArg(lean_object* v_inst_3038_, lean_object* v_x_3039_){
_start:
{
lean_object* v___f_3040_; lean_object* v___x_3041_; 
v___f_3040_ = ((lean_object*)(l_Lean_Meta_Sym_withoutShareCommonChecks___redArg___closed__0));
v___x_3041_ = lean_apply_3(v_inst_3038_, lean_box(0), v___f_3040_, v_x_3039_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks(lean_object* v_m_3042_, lean_object* v_00_u03b1_3043_, lean_object* v_inst_3044_, lean_object* v_x_3045_){
_start:
{
lean_object* v___x_3046_; 
v___x_3046_ = l_Lean_Meta_Sym_withoutShareCommonChecks___redArg(v_inst_3044_, v_x_3045_);
return v___x_3046_;
}
}
lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(lean_object* v_a_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v_config_3050_; lean_object* v___x_3051_; lean_object* v_env_3052_; uint8_t v_enforceUnfoldReducible_3053_; uint8_t v_enforceFoldProjs_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v_config_3050_ = lean_ctor_get(v_a_3047_, 1);
v___x_3051_ = lean_st_ref_get(v_a_3048_);
v_env_3052_ = lean_ctor_get(v___x_3051_, 0);
lean_inc_ref(v_env_3052_);
lean_dec(v___x_3051_);
v_enforceUnfoldReducible_3053_ = lean_ctor_get_uint8(v_config_3050_, 1);
v_enforceFoldProjs_3054_ = lean_ctor_get_uint8(v_config_3050_, 2);
v___x_3055_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3055_, 0, v_env_3052_);
lean_ctor_set_uint8(v___x_3055_, sizeof(void*)*1, v_enforceUnfoldReducible_3053_);
lean_ctor_set_uint8(v___x_3055_, sizeof(void*)*1 + 1, v_enforceFoldProjs_3054_);
v___x_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
return v___x_3056_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3047_ = stack[0].m_obj;
lean_object* v_a_3048_ = stack[1].m_obj;
lean_object* v_res_3057_;
v_res_3057_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3047_, v_a_3048_);
stack->m_obj
 = v_res_3057_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg___boxed(lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3058_, v_a_3059_);
lean_dec(v_a_3059_);
lean_dec_ref(v_a_3058_);
return v_res_3061_;
}
}
lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx(lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_){
_start:
{
lean_object* v___x_3069_; 
v___x_3069_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3062_, v_a_3067_);
return v___x_3069_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3062_ = stack[0].m_obj;
lean_object* v_a_3063_ = stack[1].m_obj;
lean_object* v_a_3064_ = stack[2].m_obj;
lean_object* v_a_3065_ = stack[3].m_obj;
lean_object* v_a_3066_ = stack[4].m_obj;
lean_object* v_a_3067_ = stack[5].m_obj;
lean_object* v_res_3070_;
v_res_3070_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx(v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
stack->m_obj
 = v_res_3070_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___boxed(lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx(v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
lean_dec(v_a_3076_);
lean_dec_ref(v_a_3075_);
lean_dec(v_a_3074_);
lean_dec_ref(v_a_3073_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
return v_res_3078_;
}
}
lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(lean_object* v_e_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_){
_start:
{
lean_object* v_config_3086_; uint8_t v_enforceUnfoldReducible_3087_; uint8_t v_enforceFoldProjs_3088_; lean_object* v_e_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v_e_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; 
v_config_3086_ = lean_ctor_get(v_a_3080_, 1);
v_enforceUnfoldReducible_3087_ = lean_ctor_get_uint8(v_config_3086_, 1);
v_enforceFoldProjs_3088_ = lean_ctor_get_uint8(v_config_3086_, 2);
if (v_enforceUnfoldReducible_3087_ == 0)
{
v_e_3098_ = v_e_3079_;
v___y_3099_ = v_a_3081_;
v___y_3100_ = v_a_3082_;
v___y_3101_ = v_a_3083_;
v___y_3102_ = v_a_3084_;
goto v___jp_3097_;
}
else
{
lean_object* v___x_3105_; 
v___x_3105_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3079_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_a_3106_; 
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_a_3106_);
lean_dec_ref_known(v___x_3105_, 1);
v_e_3098_ = v_a_3106_;
v___y_3099_ = v_a_3081_;
v___y_3100_ = v_a_3082_;
v___y_3101_ = v_a_3083_;
v___y_3102_ = v_a_3084_;
goto v___jp_3097_;
}
else
{
return v___x_3105_;
}
}
v___jp_3089_:
{
if (v_enforceUnfoldReducible_3087_ == 0)
{
lean_object* v___x_3095_; 
v___x_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3095_, 0, v_e_3090_);
return v___x_3095_;
}
else
{
lean_object* v___x_3096_; 
v___x_3096_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
return v___x_3096_;
}
}
v___jp_3097_:
{
if (v_enforceFoldProjs_3088_ == 0)
{
v_e_3090_ = v_e_3098_;
v___y_3091_ = v___y_3099_;
v___y_3092_ = v___y_3100_;
v___y_3093_ = v___y_3101_;
v___y_3094_ = v___y_3102_;
goto v___jp_3089_;
}
else
{
lean_object* v___x_3103_; 
v___x_3103_ = l_Lean_Meta_Sym_foldProjs(v_e_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_a_3104_);
lean_dec_ref_known(v___x_3103_, 1);
v_e_3090_ = v_a_3104_;
v___y_3091_ = v___y_3099_;
v___y_3092_ = v___y_3100_;
v___y_3093_ = v___y_3101_;
v___y_3094_ = v___y_3102_;
goto v___jp_3089_;
}
else
{
return v___x_3103_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3079_ = stack[0].m_obj;
lean_object* v_a_3080_ = stack[1].m_obj;
lean_object* v_a_3081_ = stack[2].m_obj;
lean_object* v_a_3082_ = stack[3].m_obj;
lean_object* v_a_3083_ = stack[4].m_obj;
lean_object* v_a_3084_ = stack[5].m_obj;
lean_object* v_res_3107_;
v_res_3107_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
stack->m_obj
 = v_res_3107_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg___boxed(lean_object* v_e_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_);
lean_dec(v_a_3113_);
lean_dec_ref(v_a_3112_);
lean_dec(v_a_3111_);
lean_dec_ref(v_a_3110_);
lean_dec_ref(v_a_3109_);
return v_res_3115_;
}
}
lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation(lean_object* v_e_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_){
_start:
{
lean_object* v___x_3124_; 
v___x_3124_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3116_, v_a_3117_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_);
return v___x_3124_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3116_ = stack[0].m_obj;
lean_object* v_a_3117_ = stack[1].m_obj;
lean_object* v_a_3118_ = stack[2].m_obj;
lean_object* v_a_3119_ = stack[3].m_obj;
lean_object* v_a_3120_ = stack[4].m_obj;
lean_object* v_a_3121_ = stack[5].m_obj;
lean_object* v_a_3122_ = stack[6].m_obj;
lean_object* v_res_3125_;
v_res_3125_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation(v_e_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_);
stack->m_obj
 = v_res_3125_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___boxed(lean_object* v_e_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation(v_e_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_);
lean_dec(v_a_3132_);
lean_dec_ref(v_a_3131_);
lean_dec(v_a_3130_);
lean_dec_ref(v_a_3129_);
lean_dec(v_a_3128_);
lean_dec_ref(v_a_3127_);
return v_res_3134_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3135_; 
v___x_3135_ = l_instMonadEIO___redArg();
return v___x_3135_;
}
}
lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(lean_object* v_msg_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v_toApplicative_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3213_; 
v___x_3148_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0);
v___x_3149_ = l_StateRefT_x27_instMonad___redArg(v___x_3148_);
v_toApplicative_3150_ = lean_ctor_get(v___x_3149_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3213_ == 0)
{
lean_object* v_unused_3214_; 
v_unused_3214_ = lean_ctor_get(v___x_3149_, 1);
lean_dec(v_unused_3214_);
v___x_3152_ = v___x_3149_;
v_isShared_3153_ = v_isSharedCheck_3213_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_toApplicative_3150_);
lean_dec(v___x_3149_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3213_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v_toFunctor_3154_; lean_object* v_toSeq_3155_; lean_object* v_toSeqLeft_3156_; lean_object* v_toSeqRight_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3211_; 
v_toFunctor_3154_ = lean_ctor_get(v_toApplicative_3150_, 0);
v_toSeq_3155_ = lean_ctor_get(v_toApplicative_3150_, 2);
v_toSeqLeft_3156_ = lean_ctor_get(v_toApplicative_3150_, 3);
v_toSeqRight_3157_ = lean_ctor_get(v_toApplicative_3150_, 4);
v_isSharedCheck_3211_ = !lean_is_exclusive(v_toApplicative_3150_);
if (v_isSharedCheck_3211_ == 0)
{
lean_object* v_unused_3212_; 
v_unused_3212_ = lean_ctor_get(v_toApplicative_3150_, 1);
lean_dec(v_unused_3212_);
v___x_3159_ = v_toApplicative_3150_;
v_isShared_3160_ = v_isSharedCheck_3211_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_toSeqRight_3157_);
lean_inc(v_toSeqLeft_3156_);
lean_inc(v_toSeq_3155_);
lean_inc(v_toFunctor_3154_);
lean_dec(v_toApplicative_3150_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3211_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___f_3161_; lean_object* v___f_3162_; lean_object* v___f_3163_; lean_object* v___f_3164_; lean_object* v___x_3165_; lean_object* v___f_3166_; lean_object* v___f_3167_; lean_object* v___f_3168_; lean_object* v___x_3170_; 
v___f_3161_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1));
v___f_3162_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2));
lean_inc_ref(v_toFunctor_3154_);
v___f_3163_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3163_, 0, v_toFunctor_3154_);
v___f_3164_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3164_, 0, v_toFunctor_3154_);
v___x_3165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3165_, 0, v___f_3163_);
lean_ctor_set(v___x_3165_, 1, v___f_3164_);
v___f_3166_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3166_, 0, v_toSeqRight_3157_);
v___f_3167_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3167_, 0, v_toSeqLeft_3156_);
v___f_3168_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3168_, 0, v_toSeq_3155_);
if (v_isShared_3160_ == 0)
{
lean_ctor_set(v___x_3159_, 4, v___f_3166_);
lean_ctor_set(v___x_3159_, 3, v___f_3167_);
lean_ctor_set(v___x_3159_, 2, v___f_3168_);
lean_ctor_set(v___x_3159_, 1, v___f_3161_);
lean_ctor_set(v___x_3159_, 0, v___x_3165_);
v___x_3170_ = v___x_3159_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3165_);
lean_ctor_set(v_reuseFailAlloc_3210_, 1, v___f_3161_);
lean_ctor_set(v_reuseFailAlloc_3210_, 2, v___f_3168_);
lean_ctor_set(v_reuseFailAlloc_3210_, 3, v___f_3167_);
lean_ctor_set(v_reuseFailAlloc_3210_, 4, v___f_3166_);
v___x_3170_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
lean_object* v___x_3172_; 
if (v_isShared_3153_ == 0)
{
lean_ctor_set(v___x_3152_, 1, v___f_3162_);
lean_ctor_set(v___x_3152_, 0, v___x_3170_);
v___x_3172_ = v___x_3152_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___x_3170_);
lean_ctor_set(v_reuseFailAlloc_3209_, 1, v___f_3162_);
v___x_3172_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
lean_object* v___x_3173_; lean_object* v_toApplicative_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3207_; 
v___x_3173_ = l_StateRefT_x27_instMonad___redArg(v___x_3172_);
v_toApplicative_3174_ = lean_ctor_get(v___x_3173_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3207_ == 0)
{
lean_object* v_unused_3208_; 
v_unused_3208_ = lean_ctor_get(v___x_3173_, 1);
lean_dec(v_unused_3208_);
v___x_3176_ = v___x_3173_;
v_isShared_3177_ = v_isSharedCheck_3207_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_toApplicative_3174_);
lean_dec(v___x_3173_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3207_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v_toFunctor_3178_; lean_object* v_toSeq_3179_; lean_object* v_toSeqLeft_3180_; lean_object* v_toSeqRight_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3205_; 
v_toFunctor_3178_ = lean_ctor_get(v_toApplicative_3174_, 0);
v_toSeq_3179_ = lean_ctor_get(v_toApplicative_3174_, 2);
v_toSeqLeft_3180_ = lean_ctor_get(v_toApplicative_3174_, 3);
v_toSeqRight_3181_ = lean_ctor_get(v_toApplicative_3174_, 4);
v_isSharedCheck_3205_ = !lean_is_exclusive(v_toApplicative_3174_);
if (v_isSharedCheck_3205_ == 0)
{
lean_object* v_unused_3206_; 
v_unused_3206_ = lean_ctor_get(v_toApplicative_3174_, 1);
lean_dec(v_unused_3206_);
v___x_3183_ = v_toApplicative_3174_;
v_isShared_3184_ = v_isSharedCheck_3205_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_toSeqRight_3181_);
lean_inc(v_toSeqLeft_3180_);
lean_inc(v_toSeq_3179_);
lean_inc(v_toFunctor_3178_);
lean_dec(v_toApplicative_3174_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3205_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___f_3185_; lean_object* v___f_3186_; lean_object* v___f_3187_; lean_object* v___f_3188_; lean_object* v___x_3189_; lean_object* v___f_3190_; lean_object* v___f_3191_; lean_object* v___f_3192_; lean_object* v___x_3194_; 
v___f_3185_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3));
v___f_3186_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4));
lean_inc_ref(v_toFunctor_3178_);
v___f_3187_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3187_, 0, v_toFunctor_3178_);
v___f_3188_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3188_, 0, v_toFunctor_3178_);
v___x_3189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3189_, 0, v___f_3187_);
lean_ctor_set(v___x_3189_, 1, v___f_3188_);
v___f_3190_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3190_, 0, v_toSeqRight_3181_);
v___f_3191_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3191_, 0, v_toSeqLeft_3180_);
v___f_3192_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3192_, 0, v_toSeq_3179_);
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 4, v___f_3190_);
lean_ctor_set(v___x_3183_, 3, v___f_3191_);
lean_ctor_set(v___x_3183_, 2, v___f_3192_);
lean_ctor_set(v___x_3183_, 1, v___f_3185_);
lean_ctor_set(v___x_3183_, 0, v___x_3189_);
v___x_3194_ = v___x_3183_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v___x_3189_);
lean_ctor_set(v_reuseFailAlloc_3204_, 1, v___f_3185_);
lean_ctor_set(v_reuseFailAlloc_3204_, 2, v___f_3192_);
lean_ctor_set(v_reuseFailAlloc_3204_, 3, v___f_3191_);
lean_ctor_set(v_reuseFailAlloc_3204_, 4, v___f_3190_);
v___x_3194_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
lean_object* v___x_3196_; 
if (v_isShared_3177_ == 0)
{
lean_ctor_set(v___x_3176_, 1, v___f_3186_);
lean_ctor_set(v___x_3176_, 0, v___x_3194_);
v___x_3196_ = v___x_3176_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3194_);
lean_ctor_set(v_reuseFailAlloc_3203_, 1, v___f_3186_);
v___x_3196_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___f_3200_; lean_object* v___x_910__overap_3201_; lean_object* v___x_3202_; 
v___x_3197_ = l_StateRefT_x27_instMonad___redArg(v___x_3196_);
v___x_3198_ = l_Lean_instInhabitedExpr;
v___x_3199_ = l_instInhabitedOfMonad___redArg(v___x_3197_, v___x_3198_);
v___f_3200_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3200_, 0, v___x_3199_);
v___x_910__overap_3201_ = lean_panic_fn_borrowed(v___f_3200_, v_msg_3140_);
lean_dec_ref(v___f_3200_);
lean_inc(v___y_3146_);
lean_inc_ref(v___y_3145_);
lean_inc(v___y_3144_);
lean_inc_ref(v___y_3143_);
lean_inc(v___y_3142_);
lean_inc_ref(v___y_3141_);
v___x_3202_ = lean_apply_7(v___x_910__overap_3201_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, lean_box(0));
return v___x_3202_;
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
LEAN_EXPORT void l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3140_ = stack[0].m_obj;
lean_object* v___y_3141_ = stack[1].m_obj;
lean_object* v___y_3142_ = stack[2].m_obj;
lean_object* v___y_3143_ = stack[3].m_obj;
lean_object* v___y_3144_ = stack[4].m_obj;
lean_object* v___y_3145_ = stack[5].m_obj;
lean_object* v___y_3146_ = stack[6].m_obj;
lean_object* v_res_3215_;
v_res_3215_ = l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(v_msg_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
stack->m_obj
 = v_res_3215_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___boxed(lean_object* v_msg_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(v_msg_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_3225_, lean_object* v_vals_3226_, lean_object* v_i_3227_, lean_object* v_k_3228_){
_start:
{
lean_object* v___x_3229_; uint8_t v___x_3230_; 
v___x_3229_ = lean_array_get_size(v_keys_3225_);
v___x_3230_ = lean_nat_dec_lt(v_i_3227_, v___x_3229_);
if (v___x_3230_ == 0)
{
lean_object* v___x_3231_; 
lean_dec(v_i_3227_);
v___x_3231_ = lean_box(0);
return v___x_3231_;
}
else
{
lean_object* v_k_x27_3232_; uint8_t v___x_3233_; 
v_k_x27_3232_ = lean_array_fget_borrowed(v_keys_3225_, v_i_3227_);
v___x_3233_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_3228_, v_k_x27_3232_);
if (v___x_3233_ == 0)
{
lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3234_ = lean_unsigned_to_nat(1u);
v___x_3235_ = lean_nat_add(v_i_3227_, v___x_3234_);
lean_dec(v_i_3227_);
v_i_3227_ = v___x_3235_;
goto _start;
}
else
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3237_ = lean_array_fget_borrowed(v_vals_3226_, v_i_3227_);
lean_dec(v_i_3227_);
lean_inc(v___x_3237_);
lean_inc(v_k_x27_3232_);
v___x_3238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3238_, 0, v_k_x27_3232_);
lean_ctor_set(v___x_3238_, 1, v___x_3237_);
v___x_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3238_);
return v___x_3239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_3240_, lean_object* v_vals_3241_, lean_object* v_i_3242_, lean_object* v_k_3243_){
_start:
{
lean_object* v_res_3244_; 
v_res_3244_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_keys_3240_, v_vals_3241_, v_i_3242_, v_k_3243_);
lean_dec_ref(v_k_3243_);
lean_dec_ref(v_vals_3241_);
lean_dec_ref(v_keys_3240_);
return v_res_3244_;
}
}
lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(lean_object* v_x_3245_, size_t v_x_3246_, lean_object* v_x_3247_){
_start:
{
if (lean_obj_tag(v_x_3245_) == 0)
{
lean_object* v_es_3248_; lean_object* v___x_3249_; size_t v___x_3250_; size_t v___x_3251_; lean_object* v_j_3252_; lean_object* v___x_3253_; 
v_es_3248_ = lean_ctor_get(v_x_3245_, 0);
v___x_3249_ = lean_box(2);
v___x_3250_ = ((size_t)31ULL);
v___x_3251_ = lean_usize_land(v_x_3246_, v___x_3250_);
v_j_3252_ = lean_usize_to_nat(v___x_3251_);
v___x_3253_ = lean_array_get_borrowed(v___x_3249_, v_es_3248_, v_j_3252_);
lean_dec(v_j_3252_);
switch(lean_obj_tag(v___x_3253_))
{
case 0:
{
lean_object* v_key_3254_; lean_object* v_val_3255_; uint8_t v___x_3256_; 
v_key_3254_ = lean_ctor_get(v___x_3253_, 0);
v_val_3255_ = lean_ctor_get(v___x_3253_, 1);
v___x_3256_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_3247_, v_key_3254_);
if (v___x_3256_ == 0)
{
lean_object* v___x_3257_; 
v___x_3257_ = lean_box(0);
return v___x_3257_;
}
else
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
lean_inc(v_val_3255_);
lean_inc(v_key_3254_);
v___x_3258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3258_, 0, v_key_3254_);
lean_ctor_set(v___x_3258_, 1, v_val_3255_);
v___x_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3258_);
return v___x_3259_;
}
}
case 1:
{
lean_object* v_node_3260_; size_t v___x_3261_; size_t v___x_3262_; 
v_node_3260_ = lean_ctor_get(v___x_3253_, 0);
v___x_3261_ = ((size_t)5ULL);
v___x_3262_ = lean_usize_shift_right(v_x_3246_, v___x_3261_);
v_x_3245_ = v_node_3260_;
v_x_3246_ = v___x_3262_;
goto _start;
}
default: 
{
lean_object* v___x_3264_; 
v___x_3264_ = lean_box(0);
return v___x_3264_;
}
}
}
else
{
lean_object* v_ks_3265_; lean_object* v_vs_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v_ks_3265_ = lean_ctor_get(v_x_3245_, 0);
v_vs_3266_ = lean_ctor_get(v_x_3245_, 1);
v___x_3267_ = lean_unsigned_to_nat(0u);
v___x_3268_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_ks_3265_, v_vs_3266_, v___x_3267_, v_x_3247_);
return v___x_3268_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3245_ = stack[0].m_obj;
size_t v_x_3246_ = stack[1].m_num;
lean_object* v_x_3247_ = stack[2].m_obj;
lean_object* v_res_3269_;
v_res_3269_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3245_, v_x_3246_, v_x_3247_);
stack->m_obj
 = v_res_3269_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg___boxed(lean_object* v_x_3270_, lean_object* v_x_3271_, lean_object* v_x_3272_){
_start:
{
size_t v_x_1317__boxed_3273_; lean_object* v_res_3274_; 
v_x_1317__boxed_3273_ = lean_unbox_usize(v_x_3271_);
lean_dec(v_x_3271_);
v_res_3274_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3270_, v_x_1317__boxed_3273_, v_x_3272_);
lean_dec_ref(v_x_3272_);
lean_dec_ref(v_x_3270_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(lean_object* v_x_3275_, lean_object* v_x_3276_){
_start:
{
uint64_t v___x_3277_; size_t v___x_3278_; lean_object* v___x_3279_; 
v___x_3277_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_3276_);
v___x_3278_ = lean_uint64_to_usize(v___x_3277_);
v___x_3279_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3275_, v___x_3278_, v_x_3276_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg___boxed(lean_object* v_x_3280_, lean_object* v_x_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v_x_3280_, v_x_3281_);
lean_dec_ref(v_x_3281_);
lean_dec_ref(v_x_3280_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0(lean_object* v_e_3283_, lean_object* v_cache_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v___y_3286_, v_e_3283_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3288_, 0, v_cache_3284_);
lean_ctor_set(v___x_3288_, 1, v___y_3286_);
v___x_3289_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_3283_, v___y_3285_, v___x_3288_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v_a_3290_; lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3299_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 1);
v_a_3291_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3293_ = v___x_3289_;
v_isShared_3294_ = v_isSharedCheck_3299_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3290_);
lean_inc(v_a_3291_);
lean_dec(v___x_3289_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3299_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v_set_3295_; lean_object* v___x_3297_; 
v_set_3295_ = lean_ctor_get(v_a_3290_, 1);
lean_inc_ref(v_set_3295_);
lean_dec(v_a_3290_);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 1, v_set_3295_);
v___x_3297_ = v___x_3293_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_a_3291_);
lean_ctor_set(v_reuseFailAlloc_3298_, 1, v_set_3295_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
}
else
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3309_; 
v_a_3300_ = lean_ctor_get(v___x_3289_, 1);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3309_ == 0)
{
lean_object* v_unused_3310_; 
v_unused_3310_ = lean_ctor_get(v___x_3289_, 0);
lean_dec(v_unused_3310_);
v___x_3302_ = v___x_3289_;
v_isShared_3303_ = v_isSharedCheck_3309_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3289_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3309_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v_map_3304_; lean_object* v_set_3305_; lean_object* v___x_3307_; 
v_map_3304_ = lean_ctor_get(v_a_3300_, 0);
lean_inc_ref(v_map_3304_);
v_set_3305_ = lean_ctor_get(v_a_3300_, 1);
lean_inc_ref(v_set_3305_);
lean_dec(v_a_3300_);
if (v_isShared_3303_ == 0)
{
lean_ctor_set(v___x_3302_, 1, v_set_3305_);
lean_ctor_set(v___x_3302_, 0, v_map_3304_);
v___x_3307_ = v___x_3302_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_map_3304_);
lean_ctor_set(v_reuseFailAlloc_3308_, 1, v_set_3305_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
else
{
lean_object* v_val_3311_; lean_object* v_fst_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3319_; 
lean_dec_ref(v_cache_3284_);
lean_dec_ref(v_e_3283_);
v_val_3311_ = lean_ctor_get(v___x_3287_, 0);
lean_inc(v_val_3311_);
lean_dec_ref_known(v___x_3287_, 1);
v_fst_3312_ = lean_ctor_get(v_val_3311_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v_val_3311_);
if (v_isSharedCheck_3319_ == 0)
{
lean_object* v_unused_3320_; 
v_unused_3320_ = lean_ctor_get(v_val_3311_, 1);
lean_dec(v_unused_3320_);
v___x_3314_ = v_val_3311_;
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_fst_3312_);
lean_dec(v_val_3311_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3317_; 
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 1, v___y_3286_);
v___x_3317_ = v___x_3314_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_fst_3312_);
lean_ctor_set(v_reuseFailAlloc_3318_, 1, v___y_3286_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0___boxed(lean_object* v_e_3321_, lean_object* v_cache_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v_res_3325_; 
v_res_3325_ = l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0(v_e_3321_, v_cache_3322_, v___y_3323_, v___y_3324_);
lean_dec_ref(v___y_3323_);
return v_res_3325_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1(void){
_start:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3327_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__4));
v___x_3328_ = lean_unsigned_to_nat(16u);
v___x_3329_ = lean_unsigned_to_nat(399u);
v___x_3330_ = ((lean_object*)(l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__0));
v___x_3331_ = ((lean_object*)(l_Lean_Meta_Sym_SymM_run___redArg___closed__2));
v___x_3332_ = l_mkPanicMessageWithDecl(v___x_3331_, v___x_3330_, v___x_3329_, v___x_3328_, v___x_3327_);
return v___x_3332_;
}
}
lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks(lean_object* v_e_3333_, lean_object* v_cache_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_){
_start:
{
lean_object* v___f_3342_; lean_object* v___x_3343_; lean_object* v_env_3344_; uint8_t v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3358_; 
v___f_3342_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommonWithoutChecks___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3342_, 0, v_e_3333_);
lean_closure_set(v___f_3342_, 1, v_cache_3334_);
v___x_3343_ = lean_st_ref_get(v_a_3340_);
v_env_3344_ = lean_ctor_get(v___x_3343_, 0);
lean_inc_ref(v_env_3344_);
lean_dec(v___x_3343_);
v___x_3345_ = 0;
v___x_3346_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3346_, 0, v_env_3344_);
lean_ctor_set_uint8(v___x_3346_, sizeof(void*)*1, v___x_3345_);
lean_ctor_set_uint8(v___x_3346_, sizeof(void*)*1 + 1, v___x_3345_);
v___x_3347_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3342_, v___x_3346_, v_a_3336_);
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3350_ = v___x_3347_;
v_isShared_3351_ = v_isSharedCheck_3358_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3347_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3358_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
if (lean_obj_tag(v_a_3348_) == 0)
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
lean_dec_ref_known(v_a_3348_, 1);
lean_del_object(v___x_3350_);
v___x_3352_ = lean_obj_once(&l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1, &l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1_once, _init_l_Lean_Meta_Sym_shareCommonWithoutChecks___closed__1);
v___x_3353_ = l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1(v___x_3352_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_);
return v___x_3353_;
}
else
{
lean_object* v_a_3354_; lean_object* v___x_3356_; 
v_a_3354_ = lean_ctor_get(v_a_3348_, 0);
lean_inc(v_a_3354_);
lean_dec_ref_known(v_a_3348_, 1);
if (v_isShared_3351_ == 0)
{
lean_ctor_set(v___x_3350_, 0, v_a_3354_);
v___x_3356_ = v___x_3350_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_a_3354_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_shareCommonWithoutChecks_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3333_ = stack[0].m_obj;
lean_object* v_cache_3334_ = stack[1].m_obj;
lean_object* v_a_3335_ = stack[2].m_obj;
lean_object* v_a_3336_ = stack[3].m_obj;
lean_object* v_a_3337_ = stack[4].m_obj;
lean_object* v_a_3338_ = stack[5].m_obj;
lean_object* v_a_3339_ = stack[6].m_obj;
lean_object* v_a_3340_ = stack[7].m_obj;
lean_object* v_res_3359_;
v_res_3359_ = l_Lean_Meta_Sym_shareCommonWithoutChecks(v_e_3333_, v_cache_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_);
stack->m_obj
 = v_res_3359_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonWithoutChecks___boxed(lean_object* v_e_3360_, lean_object* v_cache_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l_Lean_Meta_Sym_shareCommonWithoutChecks(v_e_3360_, v_cache_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
lean_dec(v_a_3367_);
lean_dec_ref(v_a_3366_);
lean_dec(v_a_3365_);
lean_dec_ref(v_a_3364_);
lean_dec(v_a_3363_);
lean_dec_ref(v_a_3362_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0(lean_object* v_00_u03b2_3370_, lean_object* v_x_3371_, lean_object* v_x_3372_){
_start:
{
lean_object* v___x_3373_; 
v___x_3373_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v_x_3371_, v_x_3372_);
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___boxed(lean_object* v_00_u03b2_3374_, lean_object* v_x_3375_, lean_object* v_x_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0(v_00_u03b2_3374_, v_x_3375_, v_x_3376_);
lean_dec_ref(v_x_3376_);
lean_dec_ref(v_x_3375_);
return v_res_3377_;
}
}
lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0(lean_object* v_00_u03b2_3378_, lean_object* v_x_3379_, size_t v_x_3380_, lean_object* v_x_3381_){
_start:
{
lean_object* v___x_3382_; 
v___x_3382_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___redArg(v_x_3379_, v_x_3380_, v_x_3381_);
return v___x_3382_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3379_ = stack[1].m_obj;
size_t v_x_3380_ = stack[2].m_num;
lean_object* v_x_3381_ = stack[3].m_obj;
lean_object* v_res_3383_;
v_res_3383_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0(lean_box(0), v_x_3379_, v_x_3380_, v_x_3381_);
stack->m_obj
 = v_res_3383_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3384_, lean_object* v_x_3385_, lean_object* v_x_3386_, lean_object* v_x_3387_){
_start:
{
size_t v_x_1623__boxed_3388_; lean_object* v_res_3389_; 
v_x_1623__boxed_3388_ = lean_unbox_usize(v_x_3386_);
lean_dec(v_x_3386_);
v_res_3389_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0(v_00_u03b2_3384_, v_x_3385_, v_x_1623__boxed_3388_, v_x_3387_);
lean_dec_ref(v_x_3387_);
lean_dec_ref(v_x_3385_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3390_, lean_object* v_keys_3391_, lean_object* v_vals_3392_, lean_object* v_heq_3393_, lean_object* v_i_3394_, lean_object* v_k_3395_){
_start:
{
lean_object* v___x_3396_; 
v___x_3396_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___redArg(v_keys_3391_, v_vals_3392_, v_i_3394_, v_k_3395_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3397_, lean_object* v_keys_3398_, lean_object* v_vals_3399_, lean_object* v_heq_3400_, lean_object* v_i_3401_, lean_object* v_k_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0_spec__0_spec__2(v_00_u03b2_3397_, v_keys_3398_, v_vals_3399_, v_heq_3400_, v_i_3401_, v_k_3402_);
lean_dec_ref(v_k_3402_);
lean_dec_ref(v_vals_3399_);
lean_dec_ref(v_keys_3398_);
return v_res_3403_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(lean_object* v_msg_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_){
_start:
{
lean_object* v_ref_3410_; lean_object* v___x_3411_; lean_object* v_a_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3420_; 
v_ref_3410_ = lean_ctor_get(v___y_3407_, 2);
v___x_3411_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_);
v_a_3412_ = lean_ctor_get(v___x_3411_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3414_ = v___x_3411_;
v_isShared_3415_ = v_isSharedCheck_3420_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_a_3412_);
lean_dec(v___x_3411_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3420_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3416_; lean_object* v___x_3418_; 
lean_inc(v_ref_3410_);
v___x_3416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3416_, 0, v_ref_3410_);
lean_ctor_set(v___x_3416_, 1, v_a_3412_);
if (v_isShared_3415_ == 0)
{
lean_ctor_set_tag(v___x_3414_, 1);
lean_ctor_set(v___x_3414_, 0, v___x_3416_);
v___x_3418_ = v___x_3414_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3416_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3404_ = stack[0].m_obj;
lean_object* v___y_3405_ = stack[1].m_obj;
lean_object* v___y_3406_ = stack[2].m_obj;
lean_object* v___y_3407_ = stack[3].m_obj;
lean_object* v___y_3408_ = stack[4].m_obj;
lean_object* v_res_3421_;
v_res_3421_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v_msg_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_);
stack->m_obj
 = v_res_3421_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg___boxed(lean_object* v_msg_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v_msg_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
return v_res_3428_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1(void){
_start:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3430_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__0));
v___x_3431_ = l_Lean_stringToMessageData(v___x_3430_);
return v___x_3431_;
}
}
lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(lean_object* v_e_3432_, lean_object* v_cache_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_){
_start:
{
lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; uint8_t v___x_3451_; 
v___x_3451_ = l_Lean_Expr_hasLooseBVars(v_e_3432_);
if (v___x_3451_ == 0)
{
v___y_3442_ = v_a_3434_;
v___y_3443_ = v_a_3435_;
v___y_3444_ = v_a_3436_;
v___y_3445_ = v_a_3437_;
v___y_3446_ = v_a_3438_;
v___y_3447_ = v_a_3439_;
goto v___jp_3441_;
}
else
{
lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
lean_dec_ref(v_cache_3433_);
v___x_3452_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___closed__1);
v___x_3453_ = l_Lean_indentExpr(v_e_3432_);
v___x_3454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3452_);
lean_ctor_set(v___x_3454_, 1, v___x_3453_);
v___x_3455_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v___x_3454_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_);
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3458_ = v___x_3455_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3455_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3456_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
v___jp_3441_:
{
lean_object* v___x_3448_; 
v___x_3448_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairShareViolation___redArg(v_e_3432_, v___y_3442_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; lean_object* v___x_3450_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc(v_a_3449_);
lean_dec_ref_known(v___x_3448_, 1);
v___x_3450_ = l_Lean_Meta_Sym_shareCommonWithoutChecks(v_a_3449_, v_cache_3433_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
return v___x_3450_;
}
else
{
lean_dec_ref(v_cache_3433_);
return v___x_3448_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3432_ = stack[0].m_obj;
lean_object* v_cache_3433_ = stack[1].m_obj;
lean_object* v_a_3434_ = stack[2].m_obj;
lean_object* v_a_3435_ = stack[3].m_obj;
lean_object* v_a_3436_ = stack[4].m_obj;
lean_object* v_a_3437_ = stack[5].m_obj;
lean_object* v_a_3438_ = stack[6].m_obj;
lean_object* v_a_3439_ = stack[7].m_obj;
lean_object* v_res_3464_;
v_res_3464_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3432_, v_cache_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_);
stack->m_obj
 = v_res_3464_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare___boxed(lean_object* v_e_3465_, lean_object* v_cache_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3465_, v_cache_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_);
lean_dec(v_a_3472_);
lean_dec_ref(v_a_3471_);
lean_dec(v_a_3470_);
lean_dec_ref(v_a_3469_);
lean_dec(v_a_3468_);
lean_dec_ref(v_a_3467_);
return v_res_3474_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0(lean_object* v_00_u03b1_3475_, lean_object* v_msg_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
lean_object* v___x_3484_; 
v___x_3484_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___redArg(v_msg_3476_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
return v___x_3484_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3476_ = stack[1].m_obj;
lean_object* v___y_3477_ = stack[2].m_obj;
lean_object* v___y_3478_ = stack[3].m_obj;
lean_object* v___y_3479_ = stack[4].m_obj;
lean_object* v___y_3480_ = stack[5].m_obj;
lean_object* v___y_3481_ = stack[6].m_obj;
lean_object* v___y_3482_ = stack[7].m_obj;
lean_object* v_res_3485_;
v_res_3485_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0(lean_box(0), v_msg_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
stack->m_obj
 = v_res_3485_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0___boxed(lean_object* v_00_u03b1_3486_, lean_object* v_msg_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare_spec__0(v_00_u03b1_3486_, v_msg_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___lam__0(lean_object* v_e_3496_, lean_object* v___x_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v___x_3500_; 
v___x_3500_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__0___redArg(v___y_3499_, v_e_3496_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3497_);
lean_ctor_set(v___x_3501_, 1, v___y_3499_);
v___x_3502_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_3496_, v___y_3498_, v___x_3501_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3512_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 1);
v_a_3504_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3506_ = v___x_3502_;
v_isShared_3507_ = v_isSharedCheck_3512_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3503_);
lean_inc(v_a_3504_);
lean_dec(v___x_3502_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3512_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v_set_3508_; lean_object* v___x_3510_; 
v_set_3508_ = lean_ctor_get(v_a_3503_, 1);
lean_inc_ref(v_set_3508_);
lean_dec(v_a_3503_);
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 1, v_set_3508_);
v___x_3510_ = v___x_3506_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3504_);
lean_ctor_set(v_reuseFailAlloc_3511_, 1, v_set_3508_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
else
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3522_; 
v_a_3513_ = lean_ctor_get(v___x_3502_, 1);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3522_ == 0)
{
lean_object* v_unused_3523_; 
v_unused_3523_ = lean_ctor_get(v___x_3502_, 0);
lean_dec(v_unused_3523_);
v___x_3515_ = v___x_3502_;
v_isShared_3516_ = v_isSharedCheck_3522_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3502_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3522_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v_map_3517_; lean_object* v_set_3518_; lean_object* v___x_3520_; 
v_map_3517_ = lean_ctor_get(v_a_3513_, 0);
lean_inc_ref(v_map_3517_);
v_set_3518_ = lean_ctor_get(v_a_3513_, 1);
lean_inc_ref(v_set_3518_);
lean_dec(v_a_3513_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 1, v_set_3518_);
lean_ctor_set(v___x_3515_, 0, v_map_3517_);
v___x_3520_ = v___x_3515_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_map_3517_);
lean_ctor_set(v_reuseFailAlloc_3521_, 1, v_set_3518_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
}
}
else
{
lean_object* v_val_3524_; lean_object* v_fst_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
lean_dec_ref(v___x_3497_);
lean_dec_ref(v_e_3496_);
v_val_3524_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_val_3524_);
lean_dec_ref_known(v___x_3500_, 1);
v_fst_3525_ = lean_ctor_get(v_val_3524_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v_val_3524_);
if (v_isSharedCheck_3532_ == 0)
{
lean_object* v_unused_3533_; 
v_unused_3533_ = lean_ctor_get(v_val_3524_, 1);
lean_dec(v_unused_3533_);
v___x_3527_ = v_val_3524_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_fst_3525_);
lean_dec(v_val_3524_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 1, v___y_3499_);
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_fst_3525_);
lean_ctor_set(v_reuseFailAlloc_3531_, 1, v___y_3499_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___lam__0___boxed(lean_object* v_e_3534_, lean_object* v___x_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l_Lean_Meta_Sym_shareCommon___lam__0(v_e_3534_, v___x_3535_, v___y_3536_, v___y_3537_);
lean_dec_ref(v___y_3536_);
return v_res_3538_;
}
}
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object* v_e_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_){
_start:
{
lean_object* v___x_3547_; lean_object* v_a_3548_; lean_object* v___x_3549_; lean_object* v___f_3550_; lean_object* v___x_3551_; lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3562_; 
v___x_3547_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3540_, v_a_3545_);
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3548_);
lean_dec_ref(v___x_3547_);
v___x_3549_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
lean_inc_ref(v_e_3539_);
v___f_3550_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommon___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3550_, 0, v_e_3539_);
lean_closure_set(v___f_3550_, 1, v___x_3549_);
v___x_3551_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3550_, v_a_3548_, v_a_3541_);
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3554_ = v___x_3551_;
v_isShared_3555_ = v_isSharedCheck_3562_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_3551_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3562_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
if (lean_obj_tag(v_a_3552_) == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3557_; 
lean_del_object(v___x_3554_);
v_a_3556_ = lean_ctor_get(v_a_3552_, 0);
lean_inc(v_a_3556_);
lean_dec_ref_known(v_a_3552_, 1);
v___x_3557_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3539_, v_a_3556_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_);
return v___x_3557_;
}
else
{
lean_object* v_a_3558_; lean_object* v___x_3560_; 
lean_dec_ref(v_e_3539_);
v_a_3558_ = lean_ctor_get(v_a_3552_, 0);
lean_inc(v_a_3558_);
lean_dec_ref_known(v_a_3552_, 1);
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 0, v_a_3558_);
v___x_3560_ = v___x_3554_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_a_3558_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_shareCommon_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3539_ = stack[0].m_obj;
lean_object* v_a_3540_ = stack[1].m_obj;
lean_object* v_a_3541_ = stack[2].m_obj;
lean_object* v_a_3542_ = stack[3].m_obj;
lean_object* v_a_3543_ = stack[4].m_obj;
lean_object* v_a_3544_ = stack[5].m_obj;
lean_object* v_a_3545_ = stack[6].m_obj;
lean_object* v_res_3563_;
v_res_3563_ = l_Lean_Meta_Sym_shareCommon(v_e_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_);
stack->m_obj
 = v_res_3563_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___boxed(lean_object* v_e_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l_Lean_Meta_Sym_shareCommon(v_e_3564_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_);
lean_dec(v_a_3570_);
lean_dec_ref(v_a_3569_);
lean_dec(v_a_3568_);
lean_dec_ref(v_a_3567_);
lean_dec(v_a_3566_);
lean_dec_ref(v_a_3565_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___lam__0(lean_object* v_e_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v___x_3576_; 
v___x_3576_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_3573_, v___y_3574_, v___y_3575_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___lam__0___boxed(lean_object* v_e_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v_res_3580_; 
v_res_3580_ = l_Lean_Meta_Sym_shareCommonInc___lam__0(v_e_3577_, v___y_3578_, v___y_3579_);
lean_dec_ref(v___y_3578_);
return v_res_3580_;
}
}
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object* v_e_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_){
_start:
{
lean_object* v___f_3589_; lean_object* v___x_3590_; lean_object* v_a_3591_; lean_object* v___x_3592_; lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3603_; 
lean_inc_ref(v_e_3581_);
v___f_3589_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_shareCommonInc___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3589_, 0, v_e_3581_);
v___x_3590_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_checkedShareCtx___redArg(v_a_3582_, v_a_3587_);
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
lean_inc(v_a_3591_);
lean_dec_ref(v___x_3590_);
v___x_3592_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_3589_, v_a_3591_, v_a_3583_);
v_a_3593_ = lean_ctor_get(v___x_3592_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3592_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3595_ = v___x_3592_;
v_isShared_3596_ = v_isSharedCheck_3603_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_a_3593_);
lean_dec(v___x_3592_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3603_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
if (lean_obj_tag(v_a_3593_) == 0)
{
lean_object* v___x_3597_; lean_object* v___x_3598_; 
lean_dec_ref_known(v_a_3593_, 1);
lean_del_object(v___x_3595_);
v___x_3597_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_3598_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_repairAndShare(v_e_3581_, v___x_3597_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_);
return v___x_3598_;
}
else
{
lean_object* v_a_3599_; lean_object* v___x_3601_; 
lean_dec_ref(v_e_3581_);
v_a_3599_ = lean_ctor_get(v_a_3593_, 0);
lean_inc(v_a_3599_);
lean_dec_ref_known(v_a_3593_, 1);
if (v_isShared_3596_ == 0)
{
lean_ctor_set(v___x_3595_, 0, v_a_3599_);
v___x_3601_ = v___x_3595_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3599_);
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
LEAN_EXPORT void l_Lean_Meta_Sym_shareCommonInc_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3581_ = stack[0].m_obj;
lean_object* v_a_3582_ = stack[1].m_obj;
lean_object* v_a_3583_ = stack[2].m_obj;
lean_object* v_a_3584_ = stack[3].m_obj;
lean_object* v_a_3585_ = stack[4].m_obj;
lean_object* v_a_3586_ = stack[5].m_obj;
lean_object* v_a_3587_ = stack[6].m_obj;
lean_object* v_res_3604_;
v_res_3604_ = l_Lean_Meta_Sym_shareCommonInc(v_e_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_);
stack->m_obj
 = v_res_3604_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___boxed(lean_object* v_e_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_){
_start:
{
lean_object* v_res_3613_; 
v_res_3613_ = l_Lean_Meta_Sym_shareCommonInc(v_e_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_);
lean_dec(v_a_3611_);
lean_dec_ref(v_a_3610_);
lean_dec(v_a_3609_);
lean_dec_ref(v_a_3608_);
lean_dec(v_a_3607_);
lean_dec_ref(v_a_3606_);
return v_res_3613_;
}
}
lean_object* l_Lean_Meta_Sym_share(lean_object* v_e_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_){
_start:
{
lean_object* v___x_3622_; 
v___x_3622_ = l_Lean_Meta_Sym_shareCommonInc(v_e_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_);
return v___x_3622_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_share_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3614_ = stack[0].m_obj;
lean_object* v_a_3615_ = stack[1].m_obj;
lean_object* v_a_3616_ = stack[2].m_obj;
lean_object* v_a_3617_ = stack[3].m_obj;
lean_object* v_a_3618_ = stack[4].m_obj;
lean_object* v_a_3619_ = stack[5].m_obj;
lean_object* v_a_3620_ = stack[6].m_obj;
lean_object* v_res_3623_;
v_res_3623_ = l_Lean_Meta_Sym_share(v_e_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_);
stack->m_obj
 = v_res_3623_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___boxed(lean_object* v_e_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l_Lean_Meta_Sym_share(v_e_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_);
lean_dec(v_a_3630_);
lean_dec_ref(v_a_3629_);
lean_dec(v_a_3628_);
lean_dec_ref(v_a_3627_);
lean_dec(v_a_3626_);
lean_dec_ref(v_a_3625_);
return v_res_3632_;
}
}
lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg(lean_object* v_a_3633_){
_start:
{
lean_object* v___x_3635_; uint8_t v_debug_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3635_ = lean_st_ref_get(v_a_3633_);
v_debug_3636_ = lean_ctor_get_uint8(v___x_3635_, sizeof(void*)*12);
lean_dec(v___x_3635_);
v___x_3637_ = lean_box(v_debug_3636_);
v___x_3638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3637_);
return v___x_3638_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_isDebugEnabled___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3633_ = stack[0].m_obj;
lean_object* v_res_3639_;
v_res_3639_ = l_Lean_Meta_Sym_isDebugEnabled___redArg(v_a_3633_);
stack->m_obj
 = v_res_3639_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg___boxed(lean_object* v_a_3640_, lean_object* v_a_3641_){
_start:
{
lean_object* v_res_3642_; 
v_res_3642_ = l_Lean_Meta_Sym_isDebugEnabled___redArg(v_a_3640_);
lean_dec(v_a_3640_);
return v_res_3642_;
}
}
lean_object* l_Lean_Meta_Sym_isDebugEnabled(lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_){
_start:
{
lean_object* v___x_3650_; uint8_t v_debug_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3650_ = lean_st_ref_get(v_a_3644_);
v_debug_3651_ = lean_ctor_get_uint8(v___x_3650_, sizeof(void*)*12);
lean_dec(v___x_3650_);
v___x_3652_ = lean_box(v_debug_3651_);
v___x_3653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3652_);
return v___x_3653_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_isDebugEnabled_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3643_ = stack[0].m_obj;
lean_object* v_a_3644_ = stack[1].m_obj;
lean_object* v_a_3645_ = stack[2].m_obj;
lean_object* v_a_3646_ = stack[3].m_obj;
lean_object* v_a_3647_ = stack[4].m_obj;
lean_object* v_a_3648_ = stack[5].m_obj;
lean_object* v_res_3654_;
v_res_3654_ = l_Lean_Meta_Sym_isDebugEnabled(v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_);
stack->m_obj
 = v_res_3654_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___boxed(lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_){
_start:
{
lean_object* v_res_3662_; 
v_res_3662_ = l_Lean_Meta_Sym_isDebugEnabled(v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
lean_dec(v_a_3660_);
lean_dec_ref(v_a_3659_);
lean_dec(v_a_3658_);
lean_dec_ref(v_a_3657_);
lean_dec(v_a_3656_);
lean_dec_ref(v_a_3655_);
return v_res_3662_;
}
}
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object* v_a_3663_){
_start:
{
lean_object* v_config_3665_; lean_object* v___x_3666_; 
v_config_3665_ = lean_ctor_get(v_a_3663_, 1);
lean_inc_ref(v_config_3665_);
v___x_3666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3666_, 0, v_config_3665_);
return v___x_3666_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getConfig___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3663_ = stack[0].m_obj;
lean_object* v_res_3667_;
v_res_3667_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3663_);
stack->m_obj
 = v_res_3667_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg___boxed(lean_object* v_a_3668_, lean_object* v_a_3669_){
_start:
{
lean_object* v_res_3670_; 
v_res_3670_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3668_);
lean_dec_ref(v_a_3668_);
return v_res_3670_;
}
}
lean_object* l_Lean_Meta_Sym_getConfig(lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_){
_start:
{
lean_object* v___x_3678_; 
v___x_3678_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3671_);
return v___x_3678_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getConfig_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3671_ = stack[0].m_obj;
lean_object* v_a_3672_ = stack[1].m_obj;
lean_object* v_a_3673_ = stack[2].m_obj;
lean_object* v_a_3674_ = stack[3].m_obj;
lean_object* v_a_3675_ = stack[4].m_obj;
lean_object* v_a_3676_ = stack[5].m_obj;
lean_object* v_res_3679_;
v_res_3679_ = l_Lean_Meta_Sym_getConfig(v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_);
stack->m_obj
 = v_res_3679_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___boxed(lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l_Lean_Meta_Sym_getConfig(v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_);
lean_dec(v_a_3685_);
lean_dec_ref(v_a_3684_);
lean_dec(v_a_3683_);
lean_dec_ref(v_a_3682_);
lean_dec(v_a_3681_);
lean_dec_ref(v_a_3680_);
return v_res_3687_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(lean_object* v_cls_3688_, lean_object* v_msg_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_){
_start:
{
lean_object* v_ref_3695_; lean_object* v___x_3696_; lean_object* v_a_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3742_; 
v_ref_3695_ = lean_ctor_get(v___y_3692_, 2);
v___x_3696_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
v_a_3697_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3699_ = v___x_3696_;
v_isShared_3700_ = v_isSharedCheck_3742_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_a_3697_);
lean_dec(v___x_3696_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3742_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v___x_3701_; lean_object* v_traceState_3702_; lean_object* v_env_3703_; lean_object* v_nextMacroScope_3704_; lean_object* v_ngen_3705_; lean_object* v_auxDeclNGen_3706_; lean_object* v_cache_3707_; lean_object* v_recordedDeps_3708_; lean_object* v_messages_3709_; lean_object* v_infoState_3710_; lean_object* v_snapshotTasks_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3741_; 
v___x_3701_ = lean_st_ref_take(v___y_3693_);
v_traceState_3702_ = lean_ctor_get(v___x_3701_, 4);
v_env_3703_ = lean_ctor_get(v___x_3701_, 0);
v_nextMacroScope_3704_ = lean_ctor_get(v___x_3701_, 1);
v_ngen_3705_ = lean_ctor_get(v___x_3701_, 2);
v_auxDeclNGen_3706_ = lean_ctor_get(v___x_3701_, 3);
v_cache_3707_ = lean_ctor_get(v___x_3701_, 5);
v_recordedDeps_3708_ = lean_ctor_get(v___x_3701_, 6);
v_messages_3709_ = lean_ctor_get(v___x_3701_, 7);
v_infoState_3710_ = lean_ctor_get(v___x_3701_, 8);
v_snapshotTasks_3711_ = lean_ctor_get(v___x_3701_, 9);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3713_ = v___x_3701_;
v_isShared_3714_ = v_isSharedCheck_3741_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_snapshotTasks_3711_);
lean_inc(v_infoState_3710_);
lean_inc(v_messages_3709_);
lean_inc(v_recordedDeps_3708_);
lean_inc(v_cache_3707_);
lean_inc(v_traceState_3702_);
lean_inc(v_auxDeclNGen_3706_);
lean_inc(v_ngen_3705_);
lean_inc(v_nextMacroScope_3704_);
lean_inc(v_env_3703_);
lean_dec(v___x_3701_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3741_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
uint64_t v_tid_3715_; lean_object* v_traces_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3740_; 
v_tid_3715_ = lean_ctor_get_uint64(v_traceState_3702_, sizeof(void*)*1);
v_traces_3716_ = lean_ctor_get(v_traceState_3702_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v_traceState_3702_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3718_ = v_traceState_3702_;
v_isShared_3719_ = v_isSharedCheck_3740_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_traces_3716_);
lean_dec(v_traceState_3702_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3740_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; double v___x_3722_; uint8_t v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3731_; 
v___x_3720_ = lean_box(0);
v___x_3721_ = lean_box(0);
v___x_3722_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_3723_ = 0;
v___x_3724_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_3725_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3725_, 0, v_cls_3688_);
lean_ctor_set(v___x_3725_, 1, v___x_3721_);
lean_ctor_set(v___x_3725_, 2, v___x_3724_);
lean_ctor_set_float(v___x_3725_, sizeof(void*)*3, v___x_3722_);
lean_ctor_set_float(v___x_3725_, sizeof(void*)*3 + 8, v___x_3722_);
lean_ctor_set_uint8(v___x_3725_, sizeof(void*)*3 + 16, v___x_3723_);
v___x_3726_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
v___x_3727_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3725_);
lean_ctor_set(v___x_3727_, 1, v_a_3697_);
lean_ctor_set(v___x_3727_, 2, v___x_3726_);
lean_inc(v_ref_3695_);
v___x_3728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3728_, 0, v_ref_3695_);
lean_ctor_set(v___x_3728_, 1, v___x_3727_);
v___x_3729_ = l_Lean_PersistentArray_push___redArg(v_traces_3716_, v___x_3728_);
if (v_isShared_3719_ == 0)
{
lean_ctor_set(v___x_3718_, 0, v___x_3729_);
v___x_3731_ = v___x_3718_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3729_);
lean_ctor_set_uint64(v_reuseFailAlloc_3739_, sizeof(void*)*1, v_tid_3715_);
v___x_3731_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
lean_object* v___x_3733_; 
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 4, v___x_3731_);
v___x_3733_ = v___x_3713_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_env_3703_);
lean_ctor_set(v_reuseFailAlloc_3738_, 1, v_nextMacroScope_3704_);
lean_ctor_set(v_reuseFailAlloc_3738_, 2, v_ngen_3705_);
lean_ctor_set(v_reuseFailAlloc_3738_, 3, v_auxDeclNGen_3706_);
lean_ctor_set(v_reuseFailAlloc_3738_, 4, v___x_3731_);
lean_ctor_set(v_reuseFailAlloc_3738_, 5, v_cache_3707_);
lean_ctor_set(v_reuseFailAlloc_3738_, 6, v_recordedDeps_3708_);
lean_ctor_set(v_reuseFailAlloc_3738_, 7, v_messages_3709_);
lean_ctor_set(v_reuseFailAlloc_3738_, 8, v_infoState_3710_);
lean_ctor_set(v_reuseFailAlloc_3738_, 9, v_snapshotTasks_3711_);
v___x_3733_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
lean_object* v___x_3734_; lean_object* v___x_3736_; 
v___x_3734_ = lean_st_ref_put(v___y_3693_, v___x_3733_);
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 0, v___x_3720_);
v___x_3736_ = v___x_3699_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3720_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3688_ = stack[0].m_obj;
lean_object* v_msg_3689_ = stack[1].m_obj;
lean_object* v___y_3690_ = stack[2].m_obj;
lean_object* v___y_3691_ = stack[3].m_obj;
lean_object* v___y_3692_ = stack[4].m_obj;
lean_object* v___y_3693_ = stack[5].m_obj;
lean_object* v_res_3743_;
v_res_3743_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v_cls_3688_, v_msg_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
stack->m_obj
 = v_res_3743_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg___boxed(lean_object* v_cls_3744_, lean_object* v_msg_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_){
_start:
{
lean_object* v_res_3751_; 
v_res_3751_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v_cls_3744_, v_msg_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
return v_res_3751_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_reportIssue___closed__2(void){
_start:
{
lean_object* v___x_3755_; uint8_t v___x_3756_; double v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; 
v___x_3755_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_3756_ = 1;
v___x_3757_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_3758_ = lean_box(0);
v___x_3759_ = ((lean_object*)(l_Lean_Meta_Sym_reportIssue___closed__1));
v___x_3760_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3760_, 0, v___x_3759_);
lean_ctor_set(v___x_3760_, 1, v___x_3758_);
lean_ctor_set(v___x_3760_, 2, v___x_3755_);
lean_ctor_set_float(v___x_3760_, sizeof(void*)*3, v___x_3757_);
lean_ctor_set_float(v___x_3760_, sizeof(void*)*3 + 8, v___x_3757_);
lean_ctor_set_uint8(v___x_3760_, sizeof(void*)*3 + 16, v___x_3756_);
return v___x_3760_;
}
}
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object* v_msg_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_){
_start:
{
lean_object* v___x_3772_; lean_object* v_a_3773_; lean_object* v___x_3774_; lean_object* v_share_3775_; lean_object* v_maxFVar_3776_; lean_object* v_proofInstInfo_3777_; lean_object* v_proofInstInfoFVar_3778_; lean_object* v_inferType_3779_; lean_object* v_getLevel_3780_; lean_object* v_congrInfo_3781_; lean_object* v_defEqI_3782_; lean_object* v_extensions_3783_; lean_object* v_issues_3784_; lean_object* v_canon_3785_; lean_object* v_instanceOverrides_3786_; uint8_t v_debug_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3807_; 
v___x_3772_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3761_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_);
v_a_3773_ = lean_ctor_get(v___x_3772_, 0);
lean_inc(v_a_3773_);
lean_dec_ref(v___x_3772_);
v___x_3774_ = lean_st_ref_take(v_a_3763_);
v_share_3775_ = lean_ctor_get(v___x_3774_, 0);
v_maxFVar_3776_ = lean_ctor_get(v___x_3774_, 1);
v_proofInstInfo_3777_ = lean_ctor_get(v___x_3774_, 2);
v_proofInstInfoFVar_3778_ = lean_ctor_get(v___x_3774_, 3);
v_inferType_3779_ = lean_ctor_get(v___x_3774_, 4);
v_getLevel_3780_ = lean_ctor_get(v___x_3774_, 5);
v_congrInfo_3781_ = lean_ctor_get(v___x_3774_, 6);
v_defEqI_3782_ = lean_ctor_get(v___x_3774_, 7);
v_extensions_3783_ = lean_ctor_get(v___x_3774_, 8);
v_issues_3784_ = lean_ctor_get(v___x_3774_, 9);
v_canon_3785_ = lean_ctor_get(v___x_3774_, 10);
v_instanceOverrides_3786_ = lean_ctor_get(v___x_3774_, 11);
v_debug_3787_ = lean_ctor_get_uint8(v___x_3774_, sizeof(void*)*12);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3774_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3789_ = v___x_3774_;
v_isShared_3790_ = v_isSharedCheck_3807_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_instanceOverrides_3786_);
lean_inc(v_canon_3785_);
lean_inc(v_issues_3784_);
lean_inc(v_extensions_3783_);
lean_inc(v_defEqI_3782_);
lean_inc(v_congrInfo_3781_);
lean_inc(v_getLevel_3780_);
lean_inc(v_inferType_3779_);
lean_inc(v_proofInstInfoFVar_3778_);
lean_inc(v_proofInstInfo_3777_);
lean_inc(v_maxFVar_3776_);
lean_inc(v_share_3775_);
lean_dec(v___x_3774_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3807_;
goto v_resetjp_3788_;
}
v___jp_3769_:
{
lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3770_ = lean_box(0);
v___x_3771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3770_);
return v___x_3771_;
}
v_resetjp_3788_:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3796_; 
v___x_3791_ = lean_obj_once(&l_Lean_Meta_Sym_reportIssue___closed__2, &l_Lean_Meta_Sym_reportIssue___closed__2_once, _init_l_Lean_Meta_Sym_reportIssue___closed__2);
v___x_3792_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
lean_inc(v_a_3773_);
v___x_3793_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3791_);
lean_ctor_set(v___x_3793_, 1, v_a_3773_);
lean_ctor_set(v___x_3793_, 2, v___x_3792_);
v___x_3794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3793_);
lean_ctor_set(v___x_3794_, 1, v_issues_3784_);
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 9, v___x_3794_);
v___x_3796_ = v___x_3789_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_share_3775_);
lean_ctor_set(v_reuseFailAlloc_3806_, 1, v_maxFVar_3776_);
lean_ctor_set(v_reuseFailAlloc_3806_, 2, v_proofInstInfo_3777_);
lean_ctor_set(v_reuseFailAlloc_3806_, 3, v_proofInstInfoFVar_3778_);
lean_ctor_set(v_reuseFailAlloc_3806_, 4, v_inferType_3779_);
lean_ctor_set(v_reuseFailAlloc_3806_, 5, v_getLevel_3780_);
lean_ctor_set(v_reuseFailAlloc_3806_, 6, v_congrInfo_3781_);
lean_ctor_set(v_reuseFailAlloc_3806_, 7, v_defEqI_3782_);
lean_ctor_set(v_reuseFailAlloc_3806_, 8, v_extensions_3783_);
lean_ctor_set(v_reuseFailAlloc_3806_, 9, v___x_3794_);
lean_ctor_set(v_reuseFailAlloc_3806_, 10, v_canon_3785_);
lean_ctor_set(v_reuseFailAlloc_3806_, 11, v_instanceOverrides_3786_);
lean_ctor_set_uint8(v_reuseFailAlloc_3806_, sizeof(void*)*12, v_debug_3787_);
v___x_3796_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
lean_object* v___x_3797_; lean_object* v_toCold_3798_; lean_object* v_options_3799_; uint8_t v_hasTrace_3800_; 
v___x_3797_ = lean_st_ref_put(v_a_3763_, v___x_3796_);
v_toCold_3798_ = lean_ctor_get(v_a_3766_, 0);
v_options_3799_ = lean_ctor_get(v_toCold_3798_, 2);
v_hasTrace_3800_ = lean_ctor_get_uint8(v_options_3799_, sizeof(void*)*1);
if (v_hasTrace_3800_ == 0)
{
lean_dec(v_a_3773_);
goto v___jp_3769_;
}
else
{
lean_object* v_inheritedTraceOptions_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; uint8_t v___x_3804_; 
v_inheritedTraceOptions_3801_ = lean_ctor_get(v_toCold_3798_, 11);
v___x_3802_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_3803_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__1___closed__2, &l_Lean_Meta_Sym_foldProjs___lam__1___closed__2_once, _init_l_Lean_Meta_Sym_foldProjs___lam__1___closed__2);
v___x_3804_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3801_, v_options_3799_, v___x_3803_);
if (v___x_3804_ == 0)
{
lean_dec(v_a_3773_);
goto v___jp_3769_;
}
else
{
lean_object* v___x_3805_; 
v___x_3805_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v___x_3802_, v_a_3773_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_);
return v___x_3805_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_reportIssue_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3761_ = stack[0].m_obj;
lean_object* v_a_3762_ = stack[1].m_obj;
lean_object* v_a_3763_ = stack[2].m_obj;
lean_object* v_a_3764_ = stack[3].m_obj;
lean_object* v_a_3765_ = stack[4].m_obj;
lean_object* v_a_3766_ = stack[5].m_obj;
lean_object* v_a_3767_ = stack[6].m_obj;
lean_object* v_res_3808_;
v_res_3808_ = l_Lean_Meta_Sym_reportIssue(v_msg_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_);
stack->m_obj
 = v_res_3808_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue___boxed(lean_object* v_msg_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l_Lean_Meta_Sym_reportIssue(v_msg_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_);
lean_dec(v_a_3815_);
lean_dec_ref(v_a_3814_);
lean_dec(v_a_3813_);
lean_dec_ref(v_a_3812_);
lean_dec(v_a_3811_);
lean_dec_ref(v_a_3810_);
return v_res_3817_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0(lean_object* v_cls_3818_, lean_object* v_msg_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_){
_start:
{
lean_object* v___x_3827_; 
v___x_3827_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___redArg(v_cls_3818_, v_msg_3819_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
return v___x_3827_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3818_ = stack[0].m_obj;
lean_object* v_msg_3819_ = stack[1].m_obj;
lean_object* v___y_3820_ = stack[2].m_obj;
lean_object* v___y_3821_ = stack[3].m_obj;
lean_object* v___y_3822_ = stack[4].m_obj;
lean_object* v___y_3823_ = stack[5].m_obj;
lean_object* v___y_3824_ = stack[6].m_obj;
lean_object* v___y_3825_ = stack[7].m_obj;
lean_object* v_res_3828_;
v_res_3828_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0(v_cls_3818_, v_msg_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
stack->m_obj
 = v_res_3828_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0___boxed(lean_object* v_cls_3829_, lean_object* v_msg_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__0(v_cls_3829_, v_msg_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
return v_res_3838_;
}
}
lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose(lean_object* v_msg_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_){
_start:
{
lean_object* v___x_3847_; lean_object* v_a_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3858_; 
v___x_3847_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3840_);
v_a_3848_ = lean_ctor_get(v___x_3847_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3850_ = v___x_3847_;
v_isShared_3851_ = v_isSharedCheck_3858_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_a_3848_);
lean_dec(v___x_3847_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3858_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
uint8_t v_verbose_3852_; 
v_verbose_3852_ = lean_ctor_get_uint8(v_a_3848_, 0);
lean_dec(v_a_3848_);
if (v_verbose_3852_ == 0)
{
lean_object* v___x_3853_; lean_object* v___x_3855_; 
lean_dec_ref(v_msg_3839_);
v___x_3853_ = lean_box(0);
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 0, v___x_3853_);
v___x_3855_ = v___x_3850_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3853_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
else
{
lean_object* v___x_3857_; 
lean_del_object(v___x_3850_);
v___x_3857_ = l_Lean_Meta_Sym_reportIssue(v_msg_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_);
return v___x_3857_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_reportIssueIfVerbose_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3839_ = stack[0].m_obj;
lean_object* v_a_3840_ = stack[1].m_obj;
lean_object* v_a_3841_ = stack[2].m_obj;
lean_object* v_a_3842_ = stack[3].m_obj;
lean_object* v_a_3843_ = stack[4].m_obj;
lean_object* v_a_3844_ = stack[5].m_obj;
lean_object* v_a_3845_ = stack[6].m_obj;
lean_object* v_res_3859_;
v_res_3859_ = l_Lean_Meta_Sym_reportIssueIfVerbose(v_msg_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_);
stack->m_obj
 = v_res_3859_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose___boxed(lean_object* v_msg_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l_Lean_Meta_Sym_reportIssueIfVerbose(v_msg_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_);
lean_dec(v_a_3866_);
lean_dec_ref(v_a_3865_);
lean_dec(v_a_3864_);
lean_dec_ref(v_a_3863_);
lean_dec(v_a_3862_);
lean_dec_ref(v_a_3861_);
return v_res_3868_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7(void){
_start:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3884_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6));
v___x_3885_ = l_String_toRawSubstring_x27(v___x_3884_);
return v___x_3885_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24(void){
_start:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3923_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_3924_ = l_String_toRawSubstring_x27(v___x_3923_);
return v___x_3924_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30(void){
_start:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3936_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29));
v___x_3937_ = l_String_toRawSubstring_x27(v___x_3936_);
return v___x_3937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(lean_object* v_s_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_){
_start:
{
lean_object* v_msg_3964_; lean_object* v_quotContext_3965_; lean_object* v_currMacroScope_3966_; lean_object* v_ref_3967_; lean_object* v___y_3968_; lean_object* v___x_3983_; lean_object* v___x_3984_; uint8_t v___x_3985_; 
lean_inc(v_s_3960_);
v___x_3983_ = l_Lean_Syntax_getKind(v_s_3960_);
v___x_3984_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16));
v___x_3985_ = lean_name_eq(v___x_3983_, v___x_3984_);
lean_dec(v___x_3983_);
if (v___x_3985_ == 0)
{
lean_object* v_quotContext_3986_; lean_object* v_currMacroScope_3987_; lean_object* v_ref_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
v_quotContext_3986_ = lean_ctor_get(v_a_3961_, 1);
v_currMacroScope_3987_ = lean_ctor_get(v_a_3961_, 2);
v_ref_3988_ = lean_ctor_get(v_a_3961_, 5);
v___x_3989_ = l_Lean_SourceInfo_fromRef(v_ref_3988_, v___x_3985_);
v___x_3990_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18));
v___x_3991_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20));
v___x_3992_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21));
lean_inc_n(v___x_3989_, 8);
v___x_3993_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3989_);
lean_ctor_set(v___x_3993_, 1, v___x_3992_);
v___x_3994_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23));
v___x_3995_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
v___x_3996_ = lean_box(0);
lean_inc_n(v_currMacroScope_3987_, 3);
lean_inc_n(v_quotContext_3986_, 3);
v___x_3997_ = l_Lean_addMacroScope(v_quotContext_3986_, v___x_3996_, v_currMacroScope_3987_);
v___x_3998_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27));
v___x_3999_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3989_);
lean_ctor_set(v___x_3999_, 1, v___x_3995_);
lean_ctor_set(v___x_3999_, 2, v___x_3997_);
lean_ctor_set(v___x_3999_, 3, v___x_3998_);
v___x_4000_ = l_Lean_Syntax_node1(v___x_3989_, v___x_3994_, v___x_3999_);
v___x_4001_ = l_Lean_Syntax_node2(v___x_3989_, v___x_3991_, v___x_3993_, v___x_4000_);
v___x_4002_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28));
v___x_4003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4003_, 0, v___x_3989_);
lean_ctor_set(v___x_4003_, 1, v___x_4002_);
v___x_4004_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4005_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
v___x_4006_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31));
v___x_4007_ = l_Lean_addMacroScope(v_quotContext_3986_, v___x_4006_, v_currMacroScope_3987_);
v___x_4008_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36));
v___x_4009_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4009_, 0, v___x_3989_);
lean_ctor_set(v___x_4009_, 1, v___x_4005_);
lean_ctor_set(v___x_4009_, 2, v___x_4007_);
lean_ctor_set(v___x_4009_, 3, v___x_4008_);
v___x_4010_ = l_Lean_Syntax_node1(v___x_3989_, v___x_4004_, v___x_4009_);
v___x_4011_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37));
v___x_4012_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4012_, 0, v___x_3989_);
lean_ctor_set(v___x_4012_, 1, v___x_4011_);
v___x_4013_ = l_Lean_Syntax_node5(v___x_3989_, v___x_3990_, v___x_4001_, v_s_3960_, v___x_4003_, v___x_4010_, v___x_4012_);
v_msg_3964_ = v___x_4013_;
v_quotContext_3965_ = v_quotContext_3986_;
v_currMacroScope_3966_ = v_currMacroScope_3987_;
v_ref_3967_ = v_ref_3988_;
v___y_3968_ = v_a_3962_;
goto v___jp_3963_;
}
else
{
lean_object* v_quotContext_4014_; lean_object* v_currMacroScope_4015_; lean_object* v_ref_4016_; uint8_t v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
v_quotContext_4014_ = lean_ctor_get(v_a_3961_, 1);
v_currMacroScope_4015_ = lean_ctor_get(v_a_3961_, 2);
v_ref_4016_ = lean_ctor_get(v_a_3961_, 5);
v___x_4017_ = 0;
v___x_4018_ = l_Lean_SourceInfo_fromRef(v_ref_4016_, v___x_4017_);
v___x_4019_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39));
v___x_4020_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40));
lean_inc(v___x_4018_);
v___x_4021_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4018_);
lean_ctor_set(v___x_4021_, 1, v___x_4020_);
v___x_4022_ = l_Lean_Syntax_node2(v___x_4018_, v___x_4019_, v___x_4021_, v_s_3960_);
lean_inc(v_currMacroScope_4015_);
lean_inc(v_quotContext_4014_);
v_msg_3964_ = v___x_4022_;
v_quotContext_3965_ = v_quotContext_4014_;
v_currMacroScope_3966_ = v_currMacroScope_4015_;
v_ref_3967_ = v_ref_4016_;
v___y_3968_ = v_a_3962_;
goto v___jp_3963_;
}
v___jp_3963_:
{
uint8_t v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
v___x_3969_ = 0;
v___x_3970_ = l_Lean_SourceInfo_fromRef(v_ref_3967_, v___x_3969_);
v___x_3971_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3));
v___x_3972_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5));
v___x_3973_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7);
v___x_3974_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9));
v___x_3975_ = l_Lean_addMacroScope(v_quotContext_3965_, v___x_3974_, v_currMacroScope_3966_);
v___x_3976_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12));
lean_inc_n(v___x_3970_, 3);
v___x_3977_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3970_);
lean_ctor_set(v___x_3977_, 1, v___x_3973_);
lean_ctor_set(v___x_3977_, 2, v___x_3975_);
lean_ctor_set(v___x_3977_, 3, v___x_3976_);
v___x_3978_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_3979_ = l_Lean_Syntax_node1(v___x_3970_, v___x_3978_, v_msg_3964_);
v___x_3980_ = l_Lean_Syntax_node2(v___x_3970_, v___x_3972_, v___x_3977_, v___x_3979_);
v___x_3981_ = l_Lean_Syntax_node1(v___x_3970_, v___x_3971_, v___x_3980_);
v___x_3982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3981_);
lean_ctor_set(v___x_3982_, 1, v___y_3968_);
return v___x_3982_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___boxed(lean_object* v_s_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_){
_start:
{
lean_object* v_res_4026_; 
v_res_4026_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(v_s_4023_, v_a_4024_, v_a_4025_);
lean_dec_ref(v_a_4024_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(lean_object* v_x_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_){
_start:
{
lean_object* v___x_4070_; uint8_t v___x_4071_; 
v___x_4070_ = ((lean_object*)(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1));
lean_inc(v_x_4067_);
v___x_4071_ = l_Lean_Syntax_isOfKind(v_x_4067_, v___x_4070_);
if (v___x_4071_ == 0)
{
lean_object* v___x_4072_; lean_object* v___x_4073_; 
lean_dec(v_x_4067_);
v___x_4072_ = lean_box(1);
v___x_4073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4073_, 0, v___x_4072_);
lean_ctor_set(v___x_4073_, 1, v_a_4069_);
return v___x_4073_;
}
else
{
lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v_a_4077_; lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4085_; 
v___x_4074_ = lean_unsigned_to_nat(1u);
v___x_4075_ = l_Lean_Syntax_getArg(v_x_4067_, v___x_4074_);
lean_dec(v_x_4067_);
v___x_4076_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(v___x_4075_, v_a_4068_, v_a_4069_);
v_a_4077_ = lean_ctor_get(v___x_4076_, 0);
v_a_4078_ = lean_ctor_get(v___x_4076_, 1);
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4080_ = v___x_4076_;
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_inc(v_a_4077_);
lean_dec(v___x_4076_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4083_; 
if (v_isShared_4081_ == 0)
{
v___x_4083_ = v___x_4080_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4077_);
lean_ctor_set(v_reuseFailAlloc_4084_, 1, v_a_4078_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1___boxed(lean_object* v_x_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_){
_start:
{
lean_object* v_res_4089_; 
v_res_4089_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(v_x_4086_, v_a_4087_, v_a_4088_);
lean_dec_ref(v_a_4087_);
return v_res_4089_;
}
}
lean_object* l_Lean_Meta_Sym_reportDbgIssue(lean_object* v_msg_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_){
_start:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v_a_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4118_; 
v___x_4098_ = l_Lean_KVMap_instValueBool;
v___x_4099_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4091_);
v_a_4100_ = lean_ctor_get(v___x_4099_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4099_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4102_ = v___x_4099_;
v_isShared_4103_ = v_isSharedCheck_4118_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_a_4100_);
lean_dec(v___x_4099_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4118_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
uint8_t v_verbose_4104_; 
v_verbose_4104_ = lean_ctor_get_uint8(v_a_4100_, 0);
lean_dec(v_a_4100_);
if (v_verbose_4104_ == 0)
{
lean_object* v___x_4105_; lean_object* v___x_4107_; 
lean_dec_ref(v_msg_4090_);
v___x_4105_ = lean_box(0);
if (v_isShared_4103_ == 0)
{
lean_ctor_set(v___x_4102_, 0, v___x_4105_);
v___x_4107_ = v___x_4102_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v___x_4105_);
v___x_4107_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
return v___x_4107_;
}
}
else
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; uint8_t v___x_4112_; 
v___x_4109_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4095_);
v___x_4110_ = l_Lean_Meta_Sym_sym_debug;
v___x_4111_ = l_Lean_Option_get___redArg(v___x_4098_, v___x_4109_, v___x_4110_);
lean_dec_ref(v___x_4109_);
v___x_4112_ = lean_unbox(v___x_4111_);
lean_dec(v___x_4111_);
if (v___x_4112_ == 0)
{
lean_object* v___x_4113_; lean_object* v___x_4115_; 
lean_dec_ref(v_msg_4090_);
v___x_4113_ = lean_box(0);
if (v_isShared_4103_ == 0)
{
lean_ctor_set(v___x_4102_, 0, v___x_4113_);
v___x_4115_ = v___x_4102_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v___x_4113_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
return v___x_4115_;
}
}
else
{
lean_object* v___x_4117_; 
lean_del_object(v___x_4102_);
v___x_4117_ = l_Lean_Meta_Sym_reportIssue(v_msg_4090_, v_a_4091_, v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_);
return v___x_4117_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_reportDbgIssue_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4090_ = stack[0].m_obj;
lean_object* v_a_4091_ = stack[1].m_obj;
lean_object* v_a_4092_ = stack[2].m_obj;
lean_object* v_a_4093_ = stack[3].m_obj;
lean_object* v_a_4094_ = stack[4].m_obj;
lean_object* v_a_4095_ = stack[5].m_obj;
lean_object* v_a_4096_ = stack[6].m_obj;
lean_object* v_res_4119_;
v_res_4119_ = l_Lean_Meta_Sym_reportDbgIssue(v_msg_4090_, v_a_4091_, v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_);
stack->m_obj
 = v_res_4119_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue___boxed(lean_object* v_msg_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_Lean_Meta_Sym_reportDbgIssue(v_msg_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_);
lean_dec(v_a_4126_);
lean_dec_ref(v_a_4125_);
lean_dec(v_a_4124_);
lean_dec_ref(v_a_4123_);
lean_dec(v_a_4122_);
lean_dec_ref(v_a_4121_);
return v_res_4128_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1(void){
_start:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4130_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0));
v___x_4131_ = l_String_toRawSubstring_x27(v___x_4130_);
return v___x_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro(lean_object* v_s_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_){
_start:
{
lean_object* v_msg_4151_; lean_object* v_quotContext_4152_; lean_object* v_currMacroScope_4153_; lean_object* v_ref_4154_; lean_object* v___y_4155_; lean_object* v___x_4170_; lean_object* v___x_4171_; uint8_t v___x_4172_; 
lean_inc(v_s_4147_);
v___x_4170_ = l_Lean_Syntax_getKind(v_s_4147_);
v___x_4171_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16));
v___x_4172_ = lean_name_eq(v___x_4170_, v___x_4171_);
lean_dec(v___x_4170_);
if (v___x_4172_ == 0)
{
lean_object* v_quotContext_4173_; lean_object* v_currMacroScope_4174_; lean_object* v_ref_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
v_quotContext_4173_ = lean_ctor_get(v_a_4148_, 1);
v_currMacroScope_4174_ = lean_ctor_get(v_a_4148_, 2);
v_ref_4175_ = lean_ctor_get(v_a_4148_, 5);
v___x_4176_ = l_Lean_SourceInfo_fromRef(v_ref_4175_, v___x_4172_);
v___x_4177_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18));
v___x_4178_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20));
v___x_4179_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21));
lean_inc_n(v___x_4176_, 8);
v___x_4180_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4176_);
lean_ctor_set(v___x_4180_, 1, v___x_4179_);
v___x_4181_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23));
v___x_4182_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
v___x_4183_ = lean_box(0);
lean_inc_n(v_currMacroScope_4174_, 3);
lean_inc_n(v_quotContext_4173_, 3);
v___x_4184_ = l_Lean_addMacroScope(v_quotContext_4173_, v___x_4183_, v_currMacroScope_4174_);
v___x_4185_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27));
v___x_4186_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4186_, 0, v___x_4176_);
lean_ctor_set(v___x_4186_, 1, v___x_4182_);
lean_ctor_set(v___x_4186_, 2, v___x_4184_);
lean_ctor_set(v___x_4186_, 3, v___x_4185_);
v___x_4187_ = l_Lean_Syntax_node1(v___x_4176_, v___x_4181_, v___x_4186_);
v___x_4188_ = l_Lean_Syntax_node2(v___x_4176_, v___x_4178_, v___x_4180_, v___x_4187_);
v___x_4189_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28));
v___x_4190_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4176_);
lean_ctor_set(v___x_4190_, 1, v___x_4189_);
v___x_4191_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4192_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
v___x_4193_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31));
v___x_4194_ = l_Lean_addMacroScope(v_quotContext_4173_, v___x_4193_, v_currMacroScope_4174_);
v___x_4195_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36));
v___x_4196_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4176_);
lean_ctor_set(v___x_4196_, 1, v___x_4192_);
lean_ctor_set(v___x_4196_, 2, v___x_4194_);
lean_ctor_set(v___x_4196_, 3, v___x_4195_);
v___x_4197_ = l_Lean_Syntax_node1(v___x_4176_, v___x_4191_, v___x_4196_);
v___x_4198_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37));
v___x_4199_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4176_);
lean_ctor_set(v___x_4199_, 1, v___x_4198_);
v___x_4200_ = l_Lean_Syntax_node5(v___x_4176_, v___x_4177_, v___x_4188_, v_s_4147_, v___x_4190_, v___x_4197_, v___x_4199_);
v_msg_4151_ = v___x_4200_;
v_quotContext_4152_ = v_quotContext_4173_;
v_currMacroScope_4153_ = v_currMacroScope_4174_;
v_ref_4154_ = v_ref_4175_;
v___y_4155_ = v_a_4149_;
goto v___jp_4150_;
}
else
{
lean_object* v_quotContext_4201_; lean_object* v_currMacroScope_4202_; lean_object* v_ref_4203_; uint8_t v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; 
v_quotContext_4201_ = lean_ctor_get(v_a_4148_, 1);
v_currMacroScope_4202_ = lean_ctor_get(v_a_4148_, 2);
v_ref_4203_ = lean_ctor_get(v_a_4148_, 5);
v___x_4204_ = 0;
v___x_4205_ = l_Lean_SourceInfo_fromRef(v_ref_4203_, v___x_4204_);
v___x_4206_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39));
v___x_4207_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40));
lean_inc(v___x_4205_);
v___x_4208_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4208_, 0, v___x_4205_);
lean_ctor_set(v___x_4208_, 1, v___x_4207_);
v___x_4209_ = l_Lean_Syntax_node2(v___x_4205_, v___x_4206_, v___x_4208_, v_s_4147_);
lean_inc(v_currMacroScope_4202_);
lean_inc(v_quotContext_4201_);
v_msg_4151_ = v___x_4209_;
v_quotContext_4152_ = v_quotContext_4201_;
v_currMacroScope_4153_ = v_currMacroScope_4202_;
v_ref_4154_ = v_ref_4203_;
v___y_4155_ = v_a_4149_;
goto v___jp_4150_;
}
v___jp_4150_:
{
uint8_t v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; 
v___x_4156_ = 0;
v___x_4157_ = l_Lean_SourceInfo_fromRef(v_ref_4154_, v___x_4156_);
v___x_4158_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3));
v___x_4159_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5));
v___x_4160_ = lean_obj_once(&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1, &l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1_once, _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1);
v___x_4161_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3));
v___x_4162_ = l_Lean_addMacroScope(v_quotContext_4152_, v___x_4161_, v_currMacroScope_4153_);
v___x_4163_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6));
lean_inc_n(v___x_4157_, 3);
v___x_4164_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4157_);
lean_ctor_set(v___x_4164_, 1, v___x_4160_);
lean_ctor_set(v___x_4164_, 2, v___x_4162_);
lean_ctor_set(v___x_4164_, 3, v___x_4163_);
v___x_4165_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_4166_ = l_Lean_Syntax_node1(v___x_4157_, v___x_4165_, v_msg_4151_);
v___x_4167_ = l_Lean_Syntax_node2(v___x_4157_, v___x_4159_, v___x_4164_, v___x_4166_);
v___x_4168_ = l_Lean_Syntax_node1(v___x_4157_, v___x_4158_, v___x_4167_);
v___x_4169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4168_);
lean_ctor_set(v___x_4169_, 1, v___y_4155_);
return v___x_4169_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___boxed(lean_object* v_s_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_){
_start:
{
lean_object* v_res_4213_; 
v_res_4213_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v_s_4210_, v_a_4211_, v_a_4212_);
lean_dec_ref(v_a_4211_);
return v_res_4213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(lean_object* v_x_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_){
_start:
{
lean_object* v___x_4235_; uint8_t v___x_4236_; 
v___x_4235_ = ((lean_object*)(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1));
lean_inc(v_x_4232_);
v___x_4236_ = l_Lean_Syntax_isOfKind(v_x_4232_, v___x_4235_);
if (v___x_4236_ == 0)
{
lean_object* v___x_4237_; lean_object* v___x_4238_; 
lean_dec(v_x_4232_);
v___x_4237_ = lean_box(1);
v___x_4238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4238_, 0, v___x_4237_);
lean_ctor_set(v___x_4238_, 1, v_a_4234_);
return v___x_4238_;
}
else
{
lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v_a_4242_; lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
v___x_4239_ = lean_unsigned_to_nat(1u);
v___x_4240_ = l_Lean_Syntax_getArg(v_x_4232_, v___x_4239_);
lean_dec(v_x_4232_);
v___x_4241_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v___x_4240_, v_a_4233_, v_a_4234_);
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
v_a_4243_ = lean_ctor_get(v___x_4241_, 1);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4241_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_inc(v_a_4242_);
lean_dec(v___x_4241_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4242_);
lean_ctor_set(v_reuseFailAlloc_4249_, 1, v_a_4243_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1___boxed(lean_object* v_x_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_){
_start:
{
lean_object* v_res_4254_; 
v_res_4254_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(v_x_4251_, v_a_4252_, v_a_4253_);
lean_dec_ref(v_a_4252_);
return v_res_4254_;
}
}
lean_object* l_Lean_Meta_Sym_getIssues___redArg(lean_object* v_a_4255_){
_start:
{
lean_object* v___x_4257_; lean_object* v_issues_4258_; lean_object* v___x_4259_; 
v___x_4257_ = lean_st_ref_get(v_a_4255_);
v_issues_4258_ = lean_ctor_get(v___x_4257_, 9);
lean_inc(v_issues_4258_);
lean_dec(v___x_4257_);
v___x_4259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4259_, 0, v_issues_4258_);
return v___x_4259_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getIssues___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4255_ = stack[0].m_obj;
lean_object* v_res_4260_;
v_res_4260_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4255_);
stack->m_obj
 = v_res_4260_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg___boxed(lean_object* v_a_4261_, lean_object* v_a_4262_){
_start:
{
lean_object* v_res_4263_; 
v_res_4263_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4261_);
lean_dec(v_a_4261_);
return v_res_4263_;
}
}
lean_object* l_Lean_Meta_Sym_getIssues(lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_){
_start:
{
lean_object* v___x_4271_; 
v___x_4271_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4265_);
return v___x_4271_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getIssues_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4264_ = stack[0].m_obj;
lean_object* v_a_4265_ = stack[1].m_obj;
lean_object* v_a_4266_ = stack[2].m_obj;
lean_object* v_a_4267_ = stack[3].m_obj;
lean_object* v_a_4268_ = stack[4].m_obj;
lean_object* v_a_4269_ = stack[5].m_obj;
lean_object* v_res_4272_;
v_res_4272_ = l_Lean_Meta_Sym_getIssues(v_a_4264_, v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_);
stack->m_obj
 = v_res_4272_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___boxed(lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_){
_start:
{
lean_object* v_res_4280_; 
v_res_4280_ = l_Lean_Meta_Sym_getIssues(v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_);
lean_dec(v_a_4278_);
lean_dec_ref(v_a_4277_);
lean_dec(v_a_4276_);
lean_dec_ref(v_a_4275_);
lean_dec(v_a_4274_);
lean_dec_ref(v_a_4273_);
return v_res_4280_;
}
}
lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(lean_object* v_a_4281_, lean_object* v_issues_4282_, lean_object* v_a_x3f_4283_){
_start:
{
lean_object* v___x_4285_; lean_object* v_share_4286_; lean_object* v_maxFVar_4287_; lean_object* v_proofInstInfo_4288_; lean_object* v_proofInstInfoFVar_4289_; lean_object* v_inferType_4290_; lean_object* v_getLevel_4291_; lean_object* v_congrInfo_4292_; lean_object* v_defEqI_4293_; lean_object* v_extensions_4294_; lean_object* v_issues_4295_; lean_object* v_canon_4296_; lean_object* v_instanceOverrides_4297_; uint8_t v_debug_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4309_; 
v___x_4285_ = lean_st_ref_take(v_a_4281_);
v_share_4286_ = lean_ctor_get(v___x_4285_, 0);
v_maxFVar_4287_ = lean_ctor_get(v___x_4285_, 1);
v_proofInstInfo_4288_ = lean_ctor_get(v___x_4285_, 2);
v_proofInstInfoFVar_4289_ = lean_ctor_get(v___x_4285_, 3);
v_inferType_4290_ = lean_ctor_get(v___x_4285_, 4);
v_getLevel_4291_ = lean_ctor_get(v___x_4285_, 5);
v_congrInfo_4292_ = lean_ctor_get(v___x_4285_, 6);
v_defEqI_4293_ = lean_ctor_get(v___x_4285_, 7);
v_extensions_4294_ = lean_ctor_get(v___x_4285_, 8);
v_issues_4295_ = lean_ctor_get(v___x_4285_, 9);
v_canon_4296_ = lean_ctor_get(v___x_4285_, 10);
v_instanceOverrides_4297_ = lean_ctor_get(v___x_4285_, 11);
v_debug_4298_ = lean_ctor_get_uint8(v___x_4285_, sizeof(void*)*12);
v_isSharedCheck_4309_ = !lean_is_exclusive(v___x_4285_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4300_ = v___x_4285_;
v_isShared_4301_ = v_isSharedCheck_4309_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_instanceOverrides_4297_);
lean_inc(v_canon_4296_);
lean_inc(v_issues_4295_);
lean_inc(v_extensions_4294_);
lean_inc(v_defEqI_4293_);
lean_inc(v_congrInfo_4292_);
lean_inc(v_getLevel_4291_);
lean_inc(v_inferType_4290_);
lean_inc(v_proofInstInfoFVar_4289_);
lean_inc(v_proofInstInfo_4288_);
lean_inc(v_maxFVar_4287_);
lean_inc(v_share_4286_);
lean_dec(v___x_4285_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4309_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4305_; 
v___x_4302_ = lean_box(0);
v___x_4303_ = l_List_appendTR___redArg(v_issues_4295_, v_issues_4282_);
if (v_isShared_4301_ == 0)
{
lean_ctor_set(v___x_4300_, 9, v___x_4303_);
v___x_4305_ = v___x_4300_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_share_4286_);
lean_ctor_set(v_reuseFailAlloc_4308_, 1, v_maxFVar_4287_);
lean_ctor_set(v_reuseFailAlloc_4308_, 2, v_proofInstInfo_4288_);
lean_ctor_set(v_reuseFailAlloc_4308_, 3, v_proofInstInfoFVar_4289_);
lean_ctor_set(v_reuseFailAlloc_4308_, 4, v_inferType_4290_);
lean_ctor_set(v_reuseFailAlloc_4308_, 5, v_getLevel_4291_);
lean_ctor_set(v_reuseFailAlloc_4308_, 6, v_congrInfo_4292_);
lean_ctor_set(v_reuseFailAlloc_4308_, 7, v_defEqI_4293_);
lean_ctor_set(v_reuseFailAlloc_4308_, 8, v_extensions_4294_);
lean_ctor_set(v_reuseFailAlloc_4308_, 9, v___x_4303_);
lean_ctor_set(v_reuseFailAlloc_4308_, 10, v_canon_4296_);
lean_ctor_set(v_reuseFailAlloc_4308_, 11, v_instanceOverrides_4297_);
lean_ctor_set_uint8(v_reuseFailAlloc_4308_, sizeof(void*)*12, v_debug_4298_);
v___x_4305_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
lean_object* v___x_4306_; lean_object* v___x_4307_; 
v___x_4306_ = lean_st_ref_put(v_a_4281_, v___x_4305_);
v___x_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4302_);
return v___x_4307_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4281_ = stack[0].m_obj;
lean_object* v_issues_4282_ = stack[1].m_obj;
lean_object* v_a_x3f_4283_ = stack[2].m_obj;
lean_object* v_res_4310_;
v_res_4310_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4281_, v_issues_4282_, v_a_x3f_4283_);
stack->m_obj
 = v_res_4310_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0___boxed(lean_object* v_a_4311_, lean_object* v_issues_4312_, lean_object* v_a_x3f_4313_, lean_object* v___y_4314_){
_start:
{
lean_object* v_res_4315_; 
v_res_4315_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4311_, v_issues_4312_, v_a_x3f_4313_);
lean_dec(v_a_x3f_4313_);
lean_dec(v_a_4311_);
return v_res_4315_;
}
}
lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg(lean_object* v_x_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_){
_start:
{
lean_object* v___x_4324_; lean_object* v_issues_4325_; lean_object* v___x_4326_; lean_object* v_share_4327_; lean_object* v_maxFVar_4328_; lean_object* v_proofInstInfo_4329_; lean_object* v_proofInstInfoFVar_4330_; lean_object* v_inferType_4331_; lean_object* v_getLevel_4332_; lean_object* v_congrInfo_4333_; lean_object* v_defEqI_4334_; lean_object* v_extensions_4335_; lean_object* v_canon_4336_; lean_object* v_instanceOverrides_4337_; uint8_t v_debug_4338_; lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4376_; 
v___x_4324_ = lean_st_ref_get(v_a_4318_);
v_issues_4325_ = lean_ctor_get(v___x_4324_, 9);
lean_inc(v_issues_4325_);
lean_dec(v___x_4324_);
v___x_4326_ = lean_st_ref_take(v_a_4318_);
v_share_4327_ = lean_ctor_get(v___x_4326_, 0);
v_maxFVar_4328_ = lean_ctor_get(v___x_4326_, 1);
v_proofInstInfo_4329_ = lean_ctor_get(v___x_4326_, 2);
v_proofInstInfoFVar_4330_ = lean_ctor_get(v___x_4326_, 3);
v_inferType_4331_ = lean_ctor_get(v___x_4326_, 4);
v_getLevel_4332_ = lean_ctor_get(v___x_4326_, 5);
v_congrInfo_4333_ = lean_ctor_get(v___x_4326_, 6);
v_defEqI_4334_ = lean_ctor_get(v___x_4326_, 7);
v_extensions_4335_ = lean_ctor_get(v___x_4326_, 8);
v_canon_4336_ = lean_ctor_get(v___x_4326_, 10);
v_instanceOverrides_4337_ = lean_ctor_get(v___x_4326_, 11);
v_debug_4338_ = lean_ctor_get_uint8(v___x_4326_, sizeof(void*)*12);
v_isSharedCheck_4376_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4376_ == 0)
{
lean_object* v_unused_4377_; 
v_unused_4377_ = lean_ctor_get(v___x_4326_, 9);
lean_dec(v_unused_4377_);
v___x_4340_ = v___x_4326_;
v_isShared_4341_ = v_isSharedCheck_4376_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_instanceOverrides_4337_);
lean_inc(v_canon_4336_);
lean_inc(v_extensions_4335_);
lean_inc(v_defEqI_4334_);
lean_inc(v_congrInfo_4333_);
lean_inc(v_getLevel_4332_);
lean_inc(v_inferType_4331_);
lean_inc(v_proofInstInfoFVar_4330_);
lean_inc(v_proofInstInfo_4329_);
lean_inc(v_maxFVar_4328_);
lean_inc(v_share_4327_);
lean_dec(v___x_4326_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4376_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
lean_object* v___x_4342_; lean_object* v___x_4344_; 
v___x_4342_ = lean_box(0);
if (v_isShared_4341_ == 0)
{
lean_ctor_set(v___x_4340_, 9, v___x_4342_);
v___x_4344_ = v___x_4340_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4375_; 
v_reuseFailAlloc_4375_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_4375_, 0, v_share_4327_);
lean_ctor_set(v_reuseFailAlloc_4375_, 1, v_maxFVar_4328_);
lean_ctor_set(v_reuseFailAlloc_4375_, 2, v_proofInstInfo_4329_);
lean_ctor_set(v_reuseFailAlloc_4375_, 3, v_proofInstInfoFVar_4330_);
lean_ctor_set(v_reuseFailAlloc_4375_, 4, v_inferType_4331_);
lean_ctor_set(v_reuseFailAlloc_4375_, 5, v_getLevel_4332_);
lean_ctor_set(v_reuseFailAlloc_4375_, 6, v_congrInfo_4333_);
lean_ctor_set(v_reuseFailAlloc_4375_, 7, v_defEqI_4334_);
lean_ctor_set(v_reuseFailAlloc_4375_, 8, v_extensions_4335_);
lean_ctor_set(v_reuseFailAlloc_4375_, 9, v___x_4342_);
lean_ctor_set(v_reuseFailAlloc_4375_, 10, v_canon_4336_);
lean_ctor_set(v_reuseFailAlloc_4375_, 11, v_instanceOverrides_4337_);
lean_ctor_set_uint8(v_reuseFailAlloc_4375_, sizeof(void*)*12, v_debug_4338_);
v___x_4344_ = v_reuseFailAlloc_4375_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
lean_object* v___x_4345_; lean_object* v_r_4346_; 
v___x_4345_ = lean_st_ref_put(v_a_4318_, v___x_4344_);
lean_inc(v_a_4322_);
lean_inc_ref(v_a_4321_);
lean_inc(v_a_4320_);
lean_inc_ref(v_a_4319_);
lean_inc(v_a_4318_);
lean_inc_ref(v_a_4317_);
v_r_4346_ = lean_apply_7(v_x_4316_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_, lean_box(0));
if (lean_obj_tag(v_r_4346_) == 0)
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4363_; 
v_a_4347_ = lean_ctor_get(v_r_4346_, 0);
v_isSharedCheck_4363_ = !lean_is_exclusive(v_r_4346_);
if (v_isSharedCheck_4363_ == 0)
{
v___x_4349_ = v_r_4346_;
v_isShared_4350_ = v_isSharedCheck_4363_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v_r_4346_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4363_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4352_; 
lean_inc(v_a_4347_);
if (v_isShared_4350_ == 0)
{
lean_ctor_set_tag(v___x_4349_, 1);
v___x_4352_ = v___x_4349_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_a_4347_);
v___x_4352_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
lean_object* v___x_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4360_; 
v___x_4353_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4318_, v_issues_4325_, v___x_4352_);
lean_dec_ref(v___x_4352_);
v_isSharedCheck_4360_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4360_ == 0)
{
lean_object* v_unused_4361_; 
v_unused_4361_ = lean_ctor_get(v___x_4353_, 0);
lean_dec(v_unused_4361_);
v___x_4355_ = v___x_4353_;
v_isShared_4356_ = v_isSharedCheck_4360_;
goto v_resetjp_4354_;
}
else
{
lean_dec(v___x_4353_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4360_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v___x_4358_; 
if (v_isShared_4356_ == 0)
{
lean_ctor_set(v___x_4355_, 0, v_a_4347_);
v___x_4358_ = v___x_4355_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v_a_4347_);
v___x_4358_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
return v___x_4358_;
}
}
}
}
}
else
{
lean_object* v_a_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4373_; 
v_a_4364_ = lean_ctor_get(v_r_4346_, 0);
lean_inc(v_a_4364_);
lean_dec_ref_known(v_r_4346_, 1);
v___x_4365_ = lean_box(0);
v___x_4366_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_4318_, v_issues_4325_, v___x_4365_);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4366_);
if (v_isSharedCheck_4373_ == 0)
{
lean_object* v_unused_4374_; 
v_unused_4374_ = lean_ctor_get(v___x_4366_, 0);
lean_dec(v_unused_4374_);
v___x_4368_ = v___x_4366_;
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
else
{
lean_dec(v___x_4366_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4371_; 
if (v_isShared_4369_ == 0)
{
lean_ctor_set_tag(v___x_4368_, 1);
lean_ctor_set(v___x_4368_, 0, v_a_4364_);
v___x_4371_ = v___x_4368_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_a_4364_);
v___x_4371_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
return v___x_4371_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_withNewIssueContext___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4316_ = stack[0].m_obj;
lean_object* v_a_4317_ = stack[1].m_obj;
lean_object* v_a_4318_ = stack[2].m_obj;
lean_object* v_a_4319_ = stack[3].m_obj;
lean_object* v_a_4320_ = stack[4].m_obj;
lean_object* v_a_4321_ = stack[5].m_obj;
lean_object* v_a_4322_ = stack[6].m_obj;
lean_object* v_res_4378_;
v_res_4378_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_4316_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_);
stack->m_obj
 = v_res_4378_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___boxed(lean_object* v_x_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_){
_start:
{
lean_object* v_res_4387_; 
v_res_4387_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_4379_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_);
lean_dec(v_a_4385_);
lean_dec_ref(v_a_4384_);
lean_dec(v_a_4383_);
lean_dec_ref(v_a_4382_);
lean_dec(v_a_4381_);
lean_dec_ref(v_a_4380_);
return v_res_4387_;
}
}
lean_object* l_Lean_Meta_Sym_withNewIssueContext(lean_object* v_00_u03b1_4388_, lean_object* v_x_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_){
_start:
{
lean_object* v___x_4397_; 
v___x_4397_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_4389_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_);
return v___x_4397_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_withNewIssueContext_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4389_ = stack[1].m_obj;
lean_object* v_a_4390_ = stack[2].m_obj;
lean_object* v_a_4391_ = stack[3].m_obj;
lean_object* v_a_4392_ = stack[4].m_obj;
lean_object* v_a_4393_ = stack[5].m_obj;
lean_object* v_a_4394_ = stack[6].m_obj;
lean_object* v_a_4395_ = stack[7].m_obj;
lean_object* v_res_4398_;
v_res_4398_ = l_Lean_Meta_Sym_withNewIssueContext(lean_box(0), v_x_4389_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_);
stack->m_obj
 = v_res_4398_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___boxed(lean_object* v_00_u03b1_4399_, lean_object* v_x_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_){
_start:
{
lean_object* v_res_4408_; 
v_res_4408_ = l_Lean_Meta_Sym_withNewIssueContext(v_00_u03b1_4399_, v_x_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_);
lean_dec(v_a_4406_);
lean_dec_ref(v_a_4405_);
lean_dec(v_a_4404_);
lean_dec_ref(v_a_4403_);
lean_dec(v_a_4402_);
lean_dec_ref(v_a_4401_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4409_, lean_object* v_vals_4410_, lean_object* v_i_4411_, lean_object* v_k_4412_){
_start:
{
lean_object* v___x_4417_; uint8_t v___x_4418_; 
v___x_4417_ = lean_array_get_size(v_keys_4409_);
v___x_4418_ = lean_nat_dec_lt(v_i_4411_, v___x_4417_);
if (v___x_4418_ == 0)
{
lean_object* v___x_4419_; 
lean_dec(v_i_4411_);
v___x_4419_ = lean_box(0);
return v___x_4419_;
}
else
{
lean_object* v_fst_4420_; lean_object* v_snd_4421_; lean_object* v_k_x27_4422_; lean_object* v_fst_4423_; lean_object* v_snd_4424_; size_t v___x_4425_; size_t v___x_4426_; uint8_t v___x_4427_; 
v_fst_4420_ = lean_ctor_get(v_k_4412_, 0);
v_snd_4421_ = lean_ctor_get(v_k_4412_, 1);
v_k_x27_4422_ = lean_array_fget_borrowed(v_keys_4409_, v_i_4411_);
v_fst_4423_ = lean_ctor_get(v_k_x27_4422_, 0);
v_snd_4424_ = lean_ctor_get(v_k_x27_4422_, 1);
v___x_4425_ = lean_ptr_addr(v_fst_4420_);
v___x_4426_ = lean_ptr_addr(v_fst_4423_);
v___x_4427_ = lean_usize_dec_eq(v___x_4425_, v___x_4426_);
if (v___x_4427_ == 0)
{
goto v___jp_4413_;
}
else
{
size_t v___x_4428_; size_t v___x_4429_; uint8_t v___x_4430_; 
v___x_4428_ = lean_ptr_addr(v_snd_4421_);
v___x_4429_ = lean_ptr_addr(v_snd_4424_);
v___x_4430_ = lean_usize_dec_eq(v___x_4428_, v___x_4429_);
if (v___x_4430_ == 0)
{
goto v___jp_4413_;
}
else
{
lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4431_ = lean_array_fget_borrowed(v_vals_4410_, v_i_4411_);
lean_dec(v_i_4411_);
lean_inc(v___x_4431_);
v___x_4432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4432_, 0, v___x_4431_);
return v___x_4432_;
}
}
}
v___jp_4413_:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; 
v___x_4414_ = lean_unsigned_to_nat(1u);
v___x_4415_ = lean_nat_add(v_i_4411_, v___x_4414_);
lean_dec(v_i_4411_);
v_i_4411_ = v___x_4415_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4433_, lean_object* v_vals_4434_, lean_object* v_i_4435_, lean_object* v_k_4436_){
_start:
{
lean_object* v_res_4437_; 
v_res_4437_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_4433_, v_vals_4434_, v_i_4435_, v_k_4436_);
lean_dec_ref(v_k_4436_);
lean_dec_ref(v_vals_4434_);
lean_dec_ref(v_keys_4433_);
return v_res_4437_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(lean_object* v_x_4438_, size_t v_x_4439_, lean_object* v_x_4440_){
_start:
{
if (lean_obj_tag(v_x_4438_) == 0)
{
lean_object* v_es_4441_; lean_object* v___x_4442_; size_t v___x_4443_; size_t v___x_4444_; lean_object* v_j_4445_; lean_object* v___x_4446_; 
v_es_4441_ = lean_ctor_get(v_x_4438_, 0);
v___x_4442_ = lean_box(2);
v___x_4443_ = ((size_t)31ULL);
v___x_4444_ = lean_usize_land(v_x_4439_, v___x_4443_);
v_j_4445_ = lean_usize_to_nat(v___x_4444_);
v___x_4446_ = lean_array_get_borrowed(v___x_4442_, v_es_4441_, v_j_4445_);
lean_dec(v_j_4445_);
switch(lean_obj_tag(v___x_4446_))
{
case 0:
{
lean_object* v_key_4447_; lean_object* v_val_4448_; lean_object* v_fst_4449_; lean_object* v_snd_4450_; lean_object* v_fst_4451_; lean_object* v_snd_4452_; size_t v___x_4453_; size_t v___x_4454_; uint8_t v___x_4455_; 
v_key_4447_ = lean_ctor_get(v___x_4446_, 0);
v_val_4448_ = lean_ctor_get(v___x_4446_, 1);
v_fst_4449_ = lean_ctor_get(v_x_4440_, 0);
v_snd_4450_ = lean_ctor_get(v_x_4440_, 1);
v_fst_4451_ = lean_ctor_get(v_key_4447_, 0);
v_snd_4452_ = lean_ctor_get(v_key_4447_, 1);
v___x_4453_ = lean_ptr_addr(v_fst_4449_);
v___x_4454_ = lean_ptr_addr(v_fst_4451_);
v___x_4455_ = lean_usize_dec_eq(v___x_4453_, v___x_4454_);
if (v___x_4455_ == 0)
{
lean_object* v___x_4456_; 
v___x_4456_ = lean_box(0);
return v___x_4456_;
}
else
{
size_t v___x_4457_; size_t v___x_4458_; uint8_t v___x_4459_; 
v___x_4457_ = lean_ptr_addr(v_snd_4450_);
v___x_4458_ = lean_ptr_addr(v_snd_4452_);
v___x_4459_ = lean_usize_dec_eq(v___x_4457_, v___x_4458_);
if (v___x_4459_ == 0)
{
lean_object* v___x_4460_; 
v___x_4460_ = lean_box(0);
return v___x_4460_;
}
else
{
lean_object* v___x_4461_; 
lean_inc(v_val_4448_);
v___x_4461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4461_, 0, v_val_4448_);
return v___x_4461_;
}
}
}
case 1:
{
lean_object* v_node_4462_; size_t v___x_4463_; size_t v___x_4464_; 
v_node_4462_ = lean_ctor_get(v___x_4446_, 0);
v___x_4463_ = ((size_t)5ULL);
v___x_4464_ = lean_usize_shift_right(v_x_4439_, v___x_4463_);
v_x_4438_ = v_node_4462_;
v_x_4439_ = v___x_4464_;
goto _start;
}
default: 
{
lean_object* v___x_4466_; 
v___x_4466_ = lean_box(0);
return v___x_4466_;
}
}
}
else
{
lean_object* v_ks_4467_; lean_object* v_vs_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; 
v_ks_4467_ = lean_ctor_get(v_x_4438_, 0);
v_vs_4468_ = lean_ctor_get(v_x_4438_, 1);
v___x_4469_ = lean_unsigned_to_nat(0u);
v___x_4470_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_ks_4467_, v_vs_4468_, v___x_4469_, v_x_4440_);
return v___x_4470_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4438_ = stack[0].m_obj;
size_t v_x_4439_ = stack[1].m_num;
lean_object* v_x_4440_ = stack[2].m_obj;
lean_object* v_res_4471_;
v_res_4471_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4438_, v_x_4439_, v_x_4440_);
stack->m_obj
 = v_res_4471_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg___boxed(lean_object* v_x_4472_, lean_object* v_x_4473_, lean_object* v_x_4474_){
_start:
{
size_t v_x_2903__boxed_4475_; lean_object* v_res_4476_; 
v_x_2903__boxed_4475_ = lean_unbox_usize(v_x_4473_);
lean_dec(v_x_4473_);
v_res_4476_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4472_, v_x_2903__boxed_4475_, v_x_4474_);
lean_dec_ref(v_x_4474_);
lean_dec_ref(v_x_4472_);
return v_res_4476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(lean_object* v_x_4477_, lean_object* v_x_4478_){
_start:
{
lean_object* v_fst_4479_; lean_object* v_snd_4480_; size_t v___x_4481_; size_t v___x_4482_; size_t v___x_4483_; uint64_t v___x_4484_; size_t v___x_4485_; size_t v___x_4486_; uint64_t v___x_4487_; uint64_t v___x_4488_; size_t v___x_4489_; lean_object* v___x_4490_; 
v_fst_4479_ = lean_ctor_get(v_x_4478_, 0);
v_snd_4480_ = lean_ctor_get(v_x_4478_, 1);
v___x_4481_ = lean_ptr_addr(v_fst_4479_);
v___x_4482_ = ((size_t)3ULL);
v___x_4483_ = lean_usize_shift_right(v___x_4481_, v___x_4482_);
v___x_4484_ = lean_usize_to_uint64(v___x_4483_);
v___x_4485_ = lean_ptr_addr(v_snd_4480_);
v___x_4486_ = lean_usize_shift_right(v___x_4485_, v___x_4482_);
v___x_4487_ = lean_usize_to_uint64(v___x_4486_);
v___x_4488_ = lean_uint64_mix_hash(v___x_4484_, v___x_4487_);
v___x_4489_ = lean_uint64_to_usize(v___x_4488_);
v___x_4490_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4477_, v___x_4489_, v_x_4478_);
return v___x_4490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg___boxed(lean_object* v_x_4491_, lean_object* v_x_4492_){
_start:
{
lean_object* v_res_4493_; 
v_res_4493_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_4491_, v_x_4492_);
lean_dec_ref(v_x_4492_);
lean_dec_ref(v_x_4491_);
return v_res_4493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_4494_, lean_object* v_x_4495_, lean_object* v_x_4496_, lean_object* v_x_4497_){
_start:
{
lean_object* v_ks_4498_; lean_object* v_vs_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4535_; 
v_ks_4498_ = lean_ctor_get(v_x_4494_, 0);
v_vs_4499_ = lean_ctor_get(v_x_4494_, 1);
v_isSharedCheck_4535_ = !lean_is_exclusive(v_x_4494_);
if (v_isSharedCheck_4535_ == 0)
{
v___x_4501_ = v_x_4494_;
v_isShared_4502_ = v_isSharedCheck_4535_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_vs_4499_);
lean_inc(v_ks_4498_);
lean_dec(v_x_4494_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4535_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v___x_4510_; uint8_t v___x_4511_; 
v___x_4510_ = lean_array_get_size(v_ks_4498_);
v___x_4511_ = lean_nat_dec_lt(v_x_4495_, v___x_4510_);
if (v___x_4511_ == 0)
{
lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; 
lean_del_object(v___x_4501_);
lean_dec(v_x_4495_);
v___x_4512_ = lean_array_push(v_ks_4498_, v_x_4496_);
v___x_4513_ = lean_array_push(v_vs_4499_, v_x_4497_);
v___x_4514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4514_, 0, v___x_4512_);
lean_ctor_set(v___x_4514_, 1, v___x_4513_);
return v___x_4514_;
}
else
{
lean_object* v_fst_4515_; lean_object* v_snd_4516_; lean_object* v_k_x27_4517_; lean_object* v_fst_4518_; lean_object* v_snd_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4534_; 
v_fst_4515_ = lean_ctor_get(v_x_4496_, 0);
v_snd_4516_ = lean_ctor_get(v_x_4496_, 1);
v_k_x27_4517_ = lean_array_fget(v_ks_4498_, v_x_4495_);
v_fst_4518_ = lean_ctor_get(v_k_x27_4517_, 0);
v_snd_4519_ = lean_ctor_get(v_k_x27_4517_, 1);
v_isSharedCheck_4534_ = !lean_is_exclusive(v_k_x27_4517_);
if (v_isSharedCheck_4534_ == 0)
{
v___x_4521_ = v_k_x27_4517_;
v_isShared_4522_ = v_isSharedCheck_4534_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_snd_4519_);
lean_inc(v_fst_4518_);
lean_dec(v_k_x27_4517_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4534_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
size_t v___x_4523_; size_t v___x_4524_; uint8_t v___x_4525_; 
v___x_4523_ = lean_ptr_addr(v_fst_4515_);
v___x_4524_ = lean_ptr_addr(v_fst_4518_);
lean_dec(v_fst_4518_);
v___x_4525_ = lean_usize_dec_eq(v___x_4523_, v___x_4524_);
if (v___x_4525_ == 0)
{
lean_del_object(v___x_4521_);
lean_dec(v_snd_4519_);
goto v___jp_4503_;
}
else
{
size_t v___x_4526_; size_t v___x_4527_; uint8_t v___x_4528_; 
v___x_4526_ = lean_ptr_addr(v_snd_4516_);
v___x_4527_ = lean_ptr_addr(v_snd_4519_);
lean_dec(v_snd_4519_);
v___x_4528_ = lean_usize_dec_eq(v___x_4526_, v___x_4527_);
if (v___x_4528_ == 0)
{
lean_del_object(v___x_4521_);
goto v___jp_4503_;
}
else
{
lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4532_; 
lean_del_object(v___x_4501_);
v___x_4529_ = lean_array_fset(v_ks_4498_, v_x_4495_, v_x_4496_);
v___x_4530_ = lean_array_fset(v_vs_4499_, v_x_4495_, v_x_4497_);
lean_dec(v_x_4495_);
if (v_isShared_4522_ == 0)
{
lean_ctor_set_tag(v___x_4521_, 1);
lean_ctor_set(v___x_4521_, 1, v___x_4530_);
lean_ctor_set(v___x_4521_, 0, v___x_4529_);
v___x_4532_ = v___x_4521_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v___x_4529_);
lean_ctor_set(v_reuseFailAlloc_4533_, 1, v___x_4530_);
v___x_4532_ = v_reuseFailAlloc_4533_;
goto v_reusejp_4531_;
}
v_reusejp_4531_:
{
return v___x_4532_;
}
}
}
}
}
v___jp_4503_:
{
lean_object* v___x_4505_; 
if (v_isShared_4502_ == 0)
{
v___x_4505_ = v___x_4501_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_ks_4498_);
lean_ctor_set(v_reuseFailAlloc_4509_, 1, v_vs_4499_);
v___x_4505_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
lean_object* v___x_4506_; lean_object* v___x_4507_; 
v___x_4506_ = lean_unsigned_to_nat(1u);
v___x_4507_ = lean_nat_add(v_x_4495_, v___x_4506_);
lean_dec(v_x_4495_);
v_x_4494_ = v___x_4505_;
v_x_4495_ = v___x_4507_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(lean_object* v_n_4536_, lean_object* v_k_4537_, lean_object* v_v_4538_){
_start:
{
lean_object* v___x_4539_; lean_object* v___x_4540_; 
v___x_4539_ = lean_unsigned_to_nat(0u);
v___x_4540_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_n_4536_, v___x_4539_, v_k_4537_, v_v_4538_);
return v___x_4540_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4541_; 
v___x_4541_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_4541_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(lean_object* v_x_4542_, size_t v_x_4543_, size_t v_x_4544_, lean_object* v_x_4545_, lean_object* v_x_4546_){
_start:
{
if (lean_obj_tag(v_x_4542_) == 0)
{
lean_object* v_es_4547_; size_t v___x_4548_; size_t v___x_4549_; lean_object* v_j_4550_; lean_object* v___x_4551_; uint8_t v___x_4552_; 
v_es_4547_ = lean_ctor_get(v_x_4542_, 0);
v___x_4548_ = ((size_t)31ULL);
v___x_4549_ = lean_usize_land(v_x_4543_, v___x_4548_);
v_j_4550_ = lean_usize_to_nat(v___x_4549_);
v___x_4551_ = lean_array_get_size(v_es_4547_);
v___x_4552_ = lean_nat_dec_lt(v_j_4550_, v___x_4551_);
if (v___x_4552_ == 0)
{
lean_dec(v_j_4550_);
lean_dec(v_x_4546_);
lean_dec_ref(v_x_4545_);
return v_x_4542_;
}
else
{
lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4601_; 
lean_inc_ref(v_es_4547_);
v_isSharedCheck_4601_ = !lean_is_exclusive(v_x_4542_);
if (v_isSharedCheck_4601_ == 0)
{
lean_object* v_unused_4602_; 
v_unused_4602_ = lean_ctor_get(v_x_4542_, 0);
lean_dec(v_unused_4602_);
v___x_4554_ = v_x_4542_;
v_isShared_4555_ = v_isSharedCheck_4601_;
goto v_resetjp_4553_;
}
else
{
lean_dec(v_x_4542_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4601_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
lean_object* v_v_4556_; lean_object* v___x_4557_; lean_object* v_xs_x27_4558_; lean_object* v___y_4560_; 
v_v_4556_ = lean_array_fget(v_es_4547_, v_j_4550_);
v___x_4557_ = lean_box(0);
v_xs_x27_4558_ = lean_array_fset(v_es_4547_, v_j_4550_, v___x_4557_);
switch(lean_obj_tag(v_v_4556_))
{
case 0:
{
lean_object* v_key_4565_; lean_object* v_val_4566_; lean_object* v___x_4568_; uint8_t v_isShared_4569_; uint8_t v_isSharedCheck_4586_; 
v_key_4565_ = lean_ctor_get(v_v_4556_, 0);
v_val_4566_ = lean_ctor_get(v_v_4556_, 1);
v_isSharedCheck_4586_ = !lean_is_exclusive(v_v_4556_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4568_ = v_v_4556_;
v_isShared_4569_ = v_isSharedCheck_4586_;
goto v_resetjp_4567_;
}
else
{
lean_inc(v_val_4566_);
lean_inc(v_key_4565_);
lean_dec(v_v_4556_);
v___x_4568_ = lean_box(0);
v_isShared_4569_ = v_isSharedCheck_4586_;
goto v_resetjp_4567_;
}
v_resetjp_4567_:
{
lean_object* v_fst_4573_; lean_object* v_snd_4574_; lean_object* v_fst_4575_; lean_object* v_snd_4576_; size_t v___x_4577_; size_t v___x_4578_; uint8_t v___x_4579_; 
v_fst_4573_ = lean_ctor_get(v_x_4545_, 0);
v_snd_4574_ = lean_ctor_get(v_x_4545_, 1);
v_fst_4575_ = lean_ctor_get(v_key_4565_, 0);
v_snd_4576_ = lean_ctor_get(v_key_4565_, 1);
v___x_4577_ = lean_ptr_addr(v_fst_4573_);
v___x_4578_ = lean_ptr_addr(v_fst_4575_);
v___x_4579_ = lean_usize_dec_eq(v___x_4577_, v___x_4578_);
if (v___x_4579_ == 0)
{
lean_del_object(v___x_4568_);
goto v___jp_4570_;
}
else
{
size_t v___x_4580_; size_t v___x_4581_; uint8_t v___x_4582_; 
v___x_4580_ = lean_ptr_addr(v_snd_4574_);
v___x_4581_ = lean_ptr_addr(v_snd_4576_);
v___x_4582_ = lean_usize_dec_eq(v___x_4580_, v___x_4581_);
if (v___x_4582_ == 0)
{
lean_del_object(v___x_4568_);
goto v___jp_4570_;
}
else
{
lean_object* v___x_4584_; 
lean_dec(v_val_4566_);
lean_dec(v_key_4565_);
if (v_isShared_4569_ == 0)
{
lean_ctor_set(v___x_4568_, 1, v_x_4546_);
lean_ctor_set(v___x_4568_, 0, v_x_4545_);
v___x_4584_ = v___x_4568_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_x_4545_);
lean_ctor_set(v_reuseFailAlloc_4585_, 1, v_x_4546_);
v___x_4584_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
v___y_4560_ = v___x_4584_;
goto v___jp_4559_;
}
}
}
v___jp_4570_:
{
lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___x_4571_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4565_, v_val_4566_, v_x_4545_, v_x_4546_);
v___x_4572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4572_, 0, v___x_4571_);
v___y_4560_ = v___x_4572_;
goto v___jp_4559_;
}
}
}
case 1:
{
lean_object* v_node_4587_; lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4599_; 
v_node_4587_ = lean_ctor_get(v_v_4556_, 0);
v_isSharedCheck_4599_ = !lean_is_exclusive(v_v_4556_);
if (v_isSharedCheck_4599_ == 0)
{
v___x_4589_ = v_v_4556_;
v_isShared_4590_ = v_isSharedCheck_4599_;
goto v_resetjp_4588_;
}
else
{
lean_inc(v_node_4587_);
lean_dec(v_v_4556_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4599_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
size_t v___x_4591_; size_t v___x_4592_; size_t v___x_4593_; size_t v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4597_; 
v___x_4591_ = ((size_t)5ULL);
v___x_4592_ = lean_usize_shift_right(v_x_4543_, v___x_4591_);
v___x_4593_ = ((size_t)1ULL);
v___x_4594_ = lean_usize_add(v_x_4544_, v___x_4593_);
v___x_4595_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_node_4587_, v___x_4592_, v___x_4594_, v_x_4545_, v_x_4546_);
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 0, v___x_4595_);
v___x_4597_ = v___x_4589_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v___x_4595_);
v___x_4597_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
v___y_4560_ = v___x_4597_;
goto v___jp_4559_;
}
}
}
default: 
{
lean_object* v___x_4600_; 
v___x_4600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4600_, 0, v_x_4545_);
lean_ctor_set(v___x_4600_, 1, v_x_4546_);
v___y_4560_ = v___x_4600_;
goto v___jp_4559_;
}
}
v___jp_4559_:
{
lean_object* v___x_4561_; lean_object* v___x_4563_; 
v___x_4561_ = lean_array_fset(v_xs_x27_4558_, v_j_4550_, v___y_4560_);
lean_dec(v_j_4550_);
if (v_isShared_4555_ == 0)
{
lean_ctor_set(v___x_4554_, 0, v___x_4561_);
v___x_4563_ = v___x_4554_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v___x_4561_);
v___x_4563_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
return v___x_4563_;
}
}
}
}
}
else
{
lean_object* v_ks_4603_; lean_object* v_vs_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4622_; 
v_ks_4603_ = lean_ctor_get(v_x_4542_, 0);
v_vs_4604_ = lean_ctor_get(v_x_4542_, 1);
v_isSharedCheck_4622_ = !lean_is_exclusive(v_x_4542_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4606_ = v_x_4542_;
v_isShared_4607_ = v_isSharedCheck_4622_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_vs_4604_);
lean_inc(v_ks_4603_);
lean_dec(v_x_4542_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4622_;
goto v_resetjp_4605_;
}
v_resetjp_4605_:
{
lean_object* v___x_4609_; 
if (v_isShared_4607_ == 0)
{
v___x_4609_ = v___x_4606_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v_ks_4603_);
lean_ctor_set(v_reuseFailAlloc_4621_, 1, v_vs_4604_);
v___x_4609_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
lean_object* v_newNode_4610_; size_t v___x_4611_; uint8_t v___x_4612_; 
v_newNode_4610_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v___x_4609_, v_x_4545_, v_x_4546_);
v___x_4611_ = ((size_t)7ULL);
v___x_4612_ = lean_usize_dec_le(v___x_4611_, v_x_4544_);
if (v___x_4612_ == 0)
{
lean_object* v___x_4613_; lean_object* v___x_4614_; uint8_t v___x_4615_; 
v___x_4613_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4610_);
v___x_4614_ = lean_unsigned_to_nat(4u);
v___x_4615_ = lean_nat_dec_lt(v___x_4613_, v___x_4614_);
lean_dec(v___x_4613_);
if (v___x_4615_ == 0)
{
lean_object* v_ks_4616_; lean_object* v_vs_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; 
v_ks_4616_ = lean_ctor_get(v_newNode_4610_, 0);
lean_inc_ref(v_ks_4616_);
v_vs_4617_ = lean_ctor_get(v_newNode_4610_, 1);
lean_inc_ref(v_vs_4617_);
lean_dec_ref(v_newNode_4610_);
v___x_4618_ = lean_unsigned_to_nat(0u);
v___x_4619_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0);
v___x_4620_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_x_4544_, v_ks_4616_, v_vs_4617_, v___x_4618_, v___x_4619_);
lean_dec_ref(v_vs_4617_);
lean_dec_ref(v_ks_4616_);
return v___x_4620_;
}
else
{
return v_newNode_4610_;
}
}
else
{
return v_newNode_4610_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4542_ = stack[0].m_obj;
size_t v_x_4543_ = stack[1].m_num;
size_t v_x_4544_ = stack[2].m_num;
lean_object* v_x_4545_ = stack[3].m_obj;
lean_object* v_x_4546_ = stack[4].m_obj;
lean_object* v_res_4623_;
v_res_4623_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4542_, v_x_4543_, v_x_4544_, v_x_4545_, v_x_4546_);
stack->m_obj
 = v_res_4623_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(size_t v_depth_4624_, lean_object* v_keys_4625_, lean_object* v_vals_4626_, lean_object* v_i_4627_, lean_object* v_entries_4628_){
_start:
{
lean_object* v___x_4629_; uint8_t v___x_4630_; 
v___x_4629_ = lean_array_get_size(v_keys_4625_);
v___x_4630_ = lean_nat_dec_lt(v_i_4627_, v___x_4629_);
if (v___x_4630_ == 0)
{
lean_dec(v_i_4627_);
return v_entries_4628_;
}
else
{
lean_object* v_k_4631_; lean_object* v_fst_4632_; lean_object* v_snd_4633_; lean_object* v_v_4634_; size_t v___x_4635_; size_t v___x_4636_; size_t v___x_4637_; uint64_t v___x_4638_; size_t v___x_4639_; size_t v___x_4640_; uint64_t v___x_4641_; uint64_t v___x_4642_; size_t v_h_4643_; size_t v___x_4644_; lean_object* v___x_4645_; size_t v___x_4646_; size_t v___x_4647_; size_t v___x_4648_; size_t v_h_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; 
v_k_4631_ = lean_array_fget_borrowed(v_keys_4625_, v_i_4627_);
v_fst_4632_ = lean_ctor_get(v_k_4631_, 0);
v_snd_4633_ = lean_ctor_get(v_k_4631_, 1);
v_v_4634_ = lean_array_fget_borrowed(v_vals_4626_, v_i_4627_);
v___x_4635_ = lean_ptr_addr(v_fst_4632_);
v___x_4636_ = ((size_t)3ULL);
v___x_4637_ = lean_usize_shift_right(v___x_4635_, v___x_4636_);
v___x_4638_ = lean_usize_to_uint64(v___x_4637_);
v___x_4639_ = lean_ptr_addr(v_snd_4633_);
v___x_4640_ = lean_usize_shift_right(v___x_4639_, v___x_4636_);
v___x_4641_ = lean_usize_to_uint64(v___x_4640_);
v___x_4642_ = lean_uint64_mix_hash(v___x_4638_, v___x_4641_);
v_h_4643_ = lean_uint64_to_usize(v___x_4642_);
v___x_4644_ = ((size_t)5ULL);
v___x_4645_ = lean_unsigned_to_nat(1u);
v___x_4646_ = ((size_t)1ULL);
v___x_4647_ = lean_usize_sub(v_depth_4624_, v___x_4646_);
v___x_4648_ = lean_usize_mul(v___x_4644_, v___x_4647_);
v_h_4649_ = lean_usize_shift_right(v_h_4643_, v___x_4648_);
v___x_4650_ = lean_nat_add(v_i_4627_, v___x_4645_);
lean_dec(v_i_4627_);
lean_inc(v_v_4634_);
lean_inc(v_k_4631_);
v___x_4651_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_entries_4628_, v_h_4649_, v_depth_4624_, v_k_4631_, v_v_4634_);
v_i_4627_ = v___x_4650_;
v_entries_4628_ = v___x_4651_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_4624_ = stack[0].m_num;
lean_object* v_keys_4625_ = stack[1].m_obj;
lean_object* v_vals_4626_ = stack[2].m_obj;
lean_object* v_i_4627_ = stack[3].m_obj;
lean_object* v_entries_4628_ = stack[4].m_obj;
lean_object* v_res_4653_;
v_res_4653_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_4624_, v_keys_4625_, v_vals_4626_, v_i_4627_, v_entries_4628_);
stack->m_obj
 = v_res_4653_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_4654_, lean_object* v_keys_4655_, lean_object* v_vals_4656_, lean_object* v_i_4657_, lean_object* v_entries_4658_){
_start:
{
size_t v_depth_boxed_4659_; lean_object* v_res_4660_; 
v_depth_boxed_4659_ = lean_unbox_usize(v_depth_4654_);
lean_dec(v_depth_4654_);
v_res_4660_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_boxed_4659_, v_keys_4655_, v_vals_4656_, v_i_4657_, v_entries_4658_);
lean_dec_ref(v_vals_4656_);
lean_dec_ref(v_keys_4655_);
return v_res_4660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___boxed(lean_object* v_x_4661_, lean_object* v_x_4662_, lean_object* v_x_4663_, lean_object* v_x_4664_, lean_object* v_x_4665_){
_start:
{
size_t v_x_3203__boxed_4666_; size_t v_x_3204__boxed_4667_; lean_object* v_res_4668_; 
v_x_3203__boxed_4666_ = lean_unbox_usize(v_x_4662_);
lean_dec(v_x_4662_);
v_x_3204__boxed_4667_ = lean_unbox_usize(v_x_4663_);
lean_dec(v_x_4663_);
v_res_4668_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4661_, v_x_3203__boxed_4666_, v_x_3204__boxed_4667_, v_x_4664_, v_x_4665_);
return v_res_4668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(lean_object* v_x_4669_, lean_object* v_x_4670_, lean_object* v_x_4671_){
_start:
{
lean_object* v_fst_4672_; lean_object* v_snd_4673_; size_t v___x_4674_; size_t v___x_4675_; size_t v___x_4676_; uint64_t v___x_4677_; size_t v___x_4678_; size_t v___x_4679_; uint64_t v___x_4680_; uint64_t v___x_4681_; size_t v___x_4682_; size_t v___x_4683_; lean_object* v___x_4684_; 
v_fst_4672_ = lean_ctor_get(v_x_4670_, 0);
v_snd_4673_ = lean_ctor_get(v_x_4670_, 1);
v___x_4674_ = lean_ptr_addr(v_fst_4672_);
v___x_4675_ = ((size_t)3ULL);
v___x_4676_ = lean_usize_shift_right(v___x_4674_, v___x_4675_);
v___x_4677_ = lean_usize_to_uint64(v___x_4676_);
v___x_4678_ = lean_ptr_addr(v_snd_4673_);
v___x_4679_ = lean_usize_shift_right(v___x_4678_, v___x_4675_);
v___x_4680_ = lean_usize_to_uint64(v___x_4679_);
v___x_4681_ = lean_uint64_mix_hash(v___x_4677_, v___x_4680_);
v___x_4682_ = lean_uint64_to_usize(v___x_4681_);
v___x_4683_ = ((size_t)1ULL);
v___x_4684_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4669_, v___x_4682_, v___x_4683_, v_x_4670_, v_x_4671_);
return v___x_4684_;
}
}
lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object* v_s_4685_, lean_object* v_t_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_){
_start:
{
lean_object* v_key_4693_; lean_object* v___x_4694_; lean_object* v_defEqI_4695_; lean_object* v___x_4696_; 
lean_inc_ref(v_t_4686_);
lean_inc_ref(v_s_4685_);
v_key_4693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_4693_, 0, v_s_4685_);
lean_ctor_set(v_key_4693_, 1, v_t_4686_);
v___x_4694_ = lean_st_ref_get(v_a_4687_);
v_defEqI_4695_ = lean_ctor_get(v___x_4694_, 7);
lean_inc_ref(v_defEqI_4695_);
lean_dec(v___x_4694_);
v___x_4696_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_defEqI_4695_, v_key_4693_);
lean_dec_ref(v_defEqI_4695_);
if (lean_obj_tag(v___x_4696_) == 1)
{
lean_object* v_val_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4704_; 
lean_dec_ref_known(v_key_4693_, 2);
lean_dec_ref(v_t_4686_);
lean_dec_ref(v_s_4685_);
v_val_4697_ = lean_ctor_get(v___x_4696_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4696_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4699_ = v___x_4696_;
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_val_4697_);
lean_dec(v___x_4696_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v___x_4702_; 
if (v_isShared_4700_ == 0)
{
lean_ctor_set_tag(v___x_4699_, 0);
v___x_4702_ = v___x_4699_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v_val_4697_);
v___x_4702_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
return v___x_4702_;
}
}
}
else
{
lean_object* v___x_4705_; 
lean_dec(v___x_4696_);
v___x_4705_ = l_Lean_Meta_isDefEqI(v_s_4685_, v_t_4686_, v_a_4688_, v_a_4689_, v_a_4690_, v_a_4691_);
if (lean_obj_tag(v___x_4705_) == 0)
{
lean_object* v_a_4706_; lean_object* v___x_4708_; uint8_t v_isShared_4709_; uint8_t v_isSharedCheck_4736_; 
v_a_4706_ = lean_ctor_get(v___x_4705_, 0);
v_isSharedCheck_4736_ = !lean_is_exclusive(v___x_4705_);
if (v_isSharedCheck_4736_ == 0)
{
v___x_4708_ = v___x_4705_;
v_isShared_4709_ = v_isSharedCheck_4736_;
goto v_resetjp_4707_;
}
else
{
lean_inc(v_a_4706_);
lean_dec(v___x_4705_);
v___x_4708_ = lean_box(0);
v_isShared_4709_ = v_isSharedCheck_4736_;
goto v_resetjp_4707_;
}
v_resetjp_4707_:
{
lean_object* v___x_4710_; lean_object* v_share_4711_; lean_object* v_maxFVar_4712_; lean_object* v_proofInstInfo_4713_; lean_object* v_proofInstInfoFVar_4714_; lean_object* v_inferType_4715_; lean_object* v_getLevel_4716_; lean_object* v_congrInfo_4717_; lean_object* v_defEqI_4718_; lean_object* v_extensions_4719_; lean_object* v_issues_4720_; lean_object* v_canon_4721_; lean_object* v_instanceOverrides_4722_; uint8_t v_debug_4723_; lean_object* v___x_4725_; uint8_t v_isShared_4726_; uint8_t v_isSharedCheck_4735_; 
v___x_4710_ = lean_st_ref_take(v_a_4687_);
v_share_4711_ = lean_ctor_get(v___x_4710_, 0);
v_maxFVar_4712_ = lean_ctor_get(v___x_4710_, 1);
v_proofInstInfo_4713_ = lean_ctor_get(v___x_4710_, 2);
v_proofInstInfoFVar_4714_ = lean_ctor_get(v___x_4710_, 3);
v_inferType_4715_ = lean_ctor_get(v___x_4710_, 4);
v_getLevel_4716_ = lean_ctor_get(v___x_4710_, 5);
v_congrInfo_4717_ = lean_ctor_get(v___x_4710_, 6);
v_defEqI_4718_ = lean_ctor_get(v___x_4710_, 7);
v_extensions_4719_ = lean_ctor_get(v___x_4710_, 8);
v_issues_4720_ = lean_ctor_get(v___x_4710_, 9);
v_canon_4721_ = lean_ctor_get(v___x_4710_, 10);
v_instanceOverrides_4722_ = lean_ctor_get(v___x_4710_, 11);
v_debug_4723_ = lean_ctor_get_uint8(v___x_4710_, sizeof(void*)*12);
v_isSharedCheck_4735_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4735_ == 0)
{
v___x_4725_ = v___x_4710_;
v_isShared_4726_ = v_isSharedCheck_4735_;
goto v_resetjp_4724_;
}
else
{
lean_inc(v_instanceOverrides_4722_);
lean_inc(v_canon_4721_);
lean_inc(v_issues_4720_);
lean_inc(v_extensions_4719_);
lean_inc(v_defEqI_4718_);
lean_inc(v_congrInfo_4717_);
lean_inc(v_getLevel_4716_);
lean_inc(v_inferType_4715_);
lean_inc(v_proofInstInfoFVar_4714_);
lean_inc(v_proofInstInfo_4713_);
lean_inc(v_maxFVar_4712_);
lean_inc(v_share_4711_);
lean_dec(v___x_4710_);
v___x_4725_ = lean_box(0);
v_isShared_4726_ = v_isSharedCheck_4735_;
goto v_resetjp_4724_;
}
v_resetjp_4724_:
{
lean_object* v___x_4727_; lean_object* v___x_4729_; 
lean_inc(v_a_4706_);
v___x_4727_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_defEqI_4718_, v_key_4693_, v_a_4706_);
if (v_isShared_4726_ == 0)
{
lean_ctor_set(v___x_4725_, 7, v___x_4727_);
v___x_4729_ = v___x_4725_;
goto v_reusejp_4728_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v_share_4711_);
lean_ctor_set(v_reuseFailAlloc_4734_, 1, v_maxFVar_4712_);
lean_ctor_set(v_reuseFailAlloc_4734_, 2, v_proofInstInfo_4713_);
lean_ctor_set(v_reuseFailAlloc_4734_, 3, v_proofInstInfoFVar_4714_);
lean_ctor_set(v_reuseFailAlloc_4734_, 4, v_inferType_4715_);
lean_ctor_set(v_reuseFailAlloc_4734_, 5, v_getLevel_4716_);
lean_ctor_set(v_reuseFailAlloc_4734_, 6, v_congrInfo_4717_);
lean_ctor_set(v_reuseFailAlloc_4734_, 7, v___x_4727_);
lean_ctor_set(v_reuseFailAlloc_4734_, 8, v_extensions_4719_);
lean_ctor_set(v_reuseFailAlloc_4734_, 9, v_issues_4720_);
lean_ctor_set(v_reuseFailAlloc_4734_, 10, v_canon_4721_);
lean_ctor_set(v_reuseFailAlloc_4734_, 11, v_instanceOverrides_4722_);
lean_ctor_set_uint8(v_reuseFailAlloc_4734_, sizeof(void*)*12, v_debug_4723_);
v___x_4729_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4728_;
}
v_reusejp_4728_:
{
lean_object* v___x_4730_; lean_object* v___x_4732_; 
v___x_4730_ = lean_st_ref_put(v_a_4687_, v___x_4729_);
if (v_isShared_4709_ == 0)
{
v___x_4732_ = v___x_4708_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v_a_4706_);
v___x_4732_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
return v___x_4732_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_4693_, 2);
return v___x_4705_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_isDefEqI___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_4685_ = stack[0].m_obj;
lean_object* v_t_4686_ = stack[1].m_obj;
lean_object* v_a_4687_ = stack[2].m_obj;
lean_object* v_a_4688_ = stack[3].m_obj;
lean_object* v_a_4689_ = stack[4].m_obj;
lean_object* v_a_4690_ = stack[5].m_obj;
lean_object* v_a_4691_ = stack[6].m_obj;
lean_object* v_res_4737_;
v_res_4737_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_4685_, v_t_4686_, v_a_4687_, v_a_4688_, v_a_4689_, v_a_4690_, v_a_4691_);
stack->m_obj
 = v_res_4737_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg___boxed(lean_object* v_s_4738_, lean_object* v_t_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_){
_start:
{
lean_object* v_res_4746_; 
v_res_4746_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_4738_, v_t_4739_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_);
lean_dec(v_a_4744_);
lean_dec_ref(v_a_4743_);
lean_dec(v_a_4742_);
lean_dec_ref(v_a_4741_);
lean_dec(v_a_4740_);
return v_res_4746_;
}
}
lean_object* l_Lean_Meta_Sym_isDefEqI(lean_object* v_s_4747_, lean_object* v_t_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_){
_start:
{
lean_object* v___x_4756_; 
v___x_4756_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_4747_, v_t_4748_, v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_);
return v___x_4756_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_isDefEqI_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_4747_ = stack[0].m_obj;
lean_object* v_t_4748_ = stack[1].m_obj;
lean_object* v_a_4749_ = stack[2].m_obj;
lean_object* v_a_4750_ = stack[3].m_obj;
lean_object* v_a_4751_ = stack[4].m_obj;
lean_object* v_a_4752_ = stack[5].m_obj;
lean_object* v_a_4753_ = stack[6].m_obj;
lean_object* v_a_4754_ = stack[7].m_obj;
lean_object* v_res_4757_;
v_res_4757_ = l_Lean_Meta_Sym_isDefEqI(v_s_4747_, v_t_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_);
stack->m_obj
 = v_res_4757_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___boxed(lean_object* v_s_4758_, lean_object* v_t_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_){
_start:
{
lean_object* v_res_4767_; 
v_res_4767_ = l_Lean_Meta_Sym_isDefEqI(v_s_4758_, v_t_4759_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_);
lean_dec(v_a_4765_);
lean_dec_ref(v_a_4764_);
lean_dec(v_a_4763_);
lean_dec_ref(v_a_4762_);
lean_dec(v_a_4761_);
lean_dec_ref(v_a_4760_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(lean_object* v_00_u03b2_4768_, lean_object* v_x_4769_, lean_object* v_x_4770_){
_start:
{
lean_object* v___x_4771_; 
v___x_4771_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_4769_, v_x_4770_);
return v___x_4771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___boxed(lean_object* v_00_u03b2_4772_, lean_object* v_x_4773_, lean_object* v_x_4774_){
_start:
{
lean_object* v_res_4775_; 
v_res_4775_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(v_00_u03b2_4772_, v_x_4773_, v_x_4774_);
lean_dec_ref(v_x_4774_);
lean_dec_ref(v_x_4773_);
return v_res_4775_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1(lean_object* v_00_u03b2_4776_, lean_object* v_x_4777_, lean_object* v_x_4778_, lean_object* v_x_4779_){
_start:
{
lean_object* v___x_4780_; 
v___x_4780_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_x_4777_, v_x_4778_, v_x_4779_);
return v___x_4780_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(lean_object* v_00_u03b2_4781_, lean_object* v_x_4782_, size_t v_x_4783_, lean_object* v_x_4784_){
_start:
{
lean_object* v___x_4785_; 
v___x_4785_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4782_, v_x_4783_, v_x_4784_);
return v___x_4785_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4782_ = stack[1].m_obj;
size_t v_x_4783_ = stack[2].m_num;
lean_object* v_x_4784_ = stack[3].m_obj;
lean_object* v_res_4786_;
v_res_4786_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(lean_box(0), v_x_4782_, v_x_4783_, v_x_4784_);
stack->m_obj
 = v_res_4786_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4787_, lean_object* v_x_4788_, lean_object* v_x_4789_, lean_object* v_x_4790_){
_start:
{
size_t v_x_3661__boxed_4791_; lean_object* v_res_4792_; 
v_x_3661__boxed_4791_ = lean_unbox_usize(v_x_4789_);
lean_dec(v_x_4789_);
v_res_4792_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(v_00_u03b2_4787_, v_x_4788_, v_x_3661__boxed_4791_, v_x_4790_);
lean_dec_ref(v_x_4790_);
lean_dec_ref(v_x_4788_);
return v_res_4792_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(lean_object* v_00_u03b2_4793_, lean_object* v_x_4794_, size_t v_x_4795_, size_t v_x_4796_, lean_object* v_x_4797_, lean_object* v_x_4798_){
_start:
{
lean_object* v___x_4799_; 
v___x_4799_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4794_, v_x_4795_, v_x_4796_, v_x_4797_, v_x_4798_);
return v___x_4799_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4794_ = stack[1].m_obj;
size_t v_x_4795_ = stack[2].m_num;
size_t v_x_4796_ = stack[3].m_num;
lean_object* v_x_4797_ = stack[4].m_obj;
lean_object* v_x_4798_ = stack[5].m_obj;
lean_object* v_res_4800_;
v_res_4800_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(lean_box(0), v_x_4794_, v_x_4795_, v_x_4796_, v_x_4797_, v_x_4798_);
stack->m_obj
 = v_res_4800_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4801_, lean_object* v_x_4802_, lean_object* v_x_4803_, lean_object* v_x_4804_, lean_object* v_x_4805_, lean_object* v_x_4806_){
_start:
{
size_t v_x_3679__boxed_4807_; size_t v_x_3680__boxed_4808_; lean_object* v_res_4809_; 
v_x_3679__boxed_4807_ = lean_unbox_usize(v_x_4803_);
lean_dec(v_x_4803_);
v_x_3680__boxed_4808_ = lean_unbox_usize(v_x_4804_);
lean_dec(v_x_4804_);
v_res_4809_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(v_00_u03b2_4801_, v_x_4802_, v_x_3679__boxed_4807_, v_x_3680__boxed_4808_, v_x_4805_, v_x_4806_);
return v_res_4809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4810_, lean_object* v_keys_4811_, lean_object* v_vals_4812_, lean_object* v_heq_4813_, lean_object* v_i_4814_, lean_object* v_k_4815_){
_start:
{
lean_object* v___x_4816_; 
v___x_4816_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_4811_, v_vals_4812_, v_i_4814_, v_k_4815_);
return v___x_4816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4817_, lean_object* v_keys_4818_, lean_object* v_vals_4819_, lean_object* v_heq_4820_, lean_object* v_i_4821_, lean_object* v_k_4822_){
_start:
{
lean_object* v_res_4823_; 
v_res_4823_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(v_00_u03b2_4817_, v_keys_4818_, v_vals_4819_, v_heq_4820_, v_i_4821_, v_k_4822_);
lean_dec_ref(v_k_4822_);
lean_dec_ref(v_vals_4819_);
lean_dec_ref(v_keys_4818_);
return v_res_4823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4824_, lean_object* v_n_4825_, lean_object* v_k_4826_, lean_object* v_v_4827_){
_start:
{
lean_object* v___x_4828_; 
v___x_4828_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v_n_4825_, v_k_4826_, v_v_4827_);
return v___x_4828_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_4829_, size_t v_depth_4830_, lean_object* v_keys_4831_, lean_object* v_vals_4832_, lean_object* v_heq_4833_, lean_object* v_i_4834_, lean_object* v_entries_4835_){
_start:
{
lean_object* v___x_4836_; 
v___x_4836_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_4830_, v_keys_4831_, v_vals_4832_, v_i_4834_, v_entries_4835_);
return v___x_4836_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_depth_4830_ = stack[1].m_num;
lean_object* v_keys_4831_ = stack[2].m_obj;
lean_object* v_vals_4832_ = stack[3].m_obj;
lean_object* v_i_4834_ = stack[5].m_obj;
lean_object* v_entries_4835_ = stack[6].m_obj;
lean_object* v_res_4837_;
v_res_4837_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(lean_box(0), v_depth_4830_, v_keys_4831_, v_vals_4832_, lean_box(0), v_i_4834_, v_entries_4835_);
stack->m_obj
 = v_res_4837_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_4838_, lean_object* v_depth_4839_, lean_object* v_keys_4840_, lean_object* v_vals_4841_, lean_object* v_heq_4842_, lean_object* v_i_4843_, lean_object* v_entries_4844_){
_start:
{
size_t v_depth_boxed_4845_; lean_object* v_res_4846_; 
v_depth_boxed_4845_ = lean_unbox_usize(v_depth_4839_);
lean_dec(v_depth_4839_);
v_res_4846_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(v_00_u03b2_4838_, v_depth_boxed_4845_, v_keys_4840_, v_vals_4841_, v_heq_4842_, v_i_4843_, v_entries_4844_);
lean_dec_ref(v_vals_4841_);
lean_dec_ref(v_keys_4840_);
return v_res_4846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_4847_, lean_object* v_x_4848_, lean_object* v_x_4849_, lean_object* v_x_4850_, lean_object* v_x_4851_){
_start:
{
lean_object* v___x_4852_; 
v___x_4852_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_x_4848_, v_x_4849_, v_x_4850_, v_x_4851_);
return v___x_4852_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__0(void){
_start:
{
lean_object* v___x_4853_; lean_object* v___f_4854_; 
v___x_4853_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_4854_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4854_, 0, v___x_4853_);
return v___f_4854_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__1(void){
_start:
{
lean_object* v___x_4855_; lean_object* v___f_4856_; 
v___x_4855_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_4856_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4856_, 0, v___x_4855_);
return v___f_4856_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2(void){
_start:
{
lean_object* v___f_4857_; lean_object* v___f_4858_; lean_object* v___x_4859_; 
v___f_4857_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__1, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__1_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__1);
v___f_4858_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__0, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__0);
v___x_4859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4859_, 0, v___f_4858_);
lean_ctor_set(v___x_4859_, 1, v___f_4857_);
return v___x_4859_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__3(void){
_start:
{
lean_object* v___x_4860_; lean_object* v___f_4861_; 
v___x_4860_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2);
v___f_4861_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4861_, 0, v___x_4860_);
return v___f_4861_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__4(void){
_start:
{
lean_object* v___x_4862_; lean_object* v___f_4863_; 
v___x_4862_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__2);
v___f_4863_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4863_, 0, v___x_4862_);
return v___f_4863_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5(void){
_start:
{
lean_object* v___f_4864_; lean_object* v___f_4865_; lean_object* v___x_4866_; 
v___f_4864_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__4, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__4_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__4);
v___f_4865_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__3, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__3_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__3);
v___x_4866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4866_, 0, v___f_4865_);
lean_ctor_set(v___x_4866_, 1, v___f_4864_);
return v___x_4866_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__6(void){
_start:
{
lean_object* v___x_4867_; lean_object* v___f_4868_; 
v___x_4867_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5);
v___f_4868_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4868_, 0, v___x_4867_);
return v___f_4868_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__7(void){
_start:
{
lean_object* v___x_4869_; lean_object* v___f_4870_; 
v___x_4869_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__5);
v___f_4870_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4870_, 0, v___x_4869_);
return v___f_4870_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8(void){
_start:
{
lean_object* v___f_4871_; lean_object* v___f_4872_; lean_object* v___x_4873_; 
v___f_4871_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__7, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__7_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__7);
v___f_4872_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__6, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__6_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__6);
v___x_4873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4873_, 0, v___f_4872_);
lean_ctor_set(v___x_4873_, 1, v___f_4871_);
return v___x_4873_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__9(void){
_start:
{
lean_object* v___x_4874_; lean_object* v___f_4875_; 
v___x_4874_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8);
v___f_4875_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4875_, 0, v___x_4874_);
return v___f_4875_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__10(void){
_start:
{
lean_object* v___x_4876_; lean_object* v___f_4877_; 
v___x_4876_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__8);
v___f_4877_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_4877_, 0, v___x_4876_);
return v___f_4877_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__11(void){
_start:
{
lean_object* v___f_4878_; lean_object* v___f_4879_; lean_object* v___x_4880_; 
v___f_4878_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__10, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__10_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__10);
v___f_4879_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__9, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__9_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__9);
v___x_4880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4880_, 0, v___f_4879_);
lean_ctor_set(v___x_4880_, 1, v___f_4878_);
return v___x_4880_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__16(void){
_start:
{
lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; 
v___x_4885_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_4886_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__15));
v___x_4887_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__14));
v___x_4888_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_4887_, v___x_4886_, v___x_4885_);
return v___x_4888_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__17(void){
_start:
{
lean_object* v___x_4889_; lean_object* v___f_4890_; lean_object* v___f_4891_; lean_object* v___x_4892_; 
v___x_4889_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__16, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__16_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__16);
v___f_4890_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__13));
v___f_4891_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__12));
v___x_4892_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_4891_, v___f_4890_, v___x_4889_);
return v___x_4892_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__18(void){
_start:
{
lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; 
v___x_4893_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__17, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__17_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__17);
v___x_4894_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__15));
v___x_4895_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__14));
v___x_4896_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_4895_, v___x_4894_, v___x_4893_);
return v___x_4896_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__19(void){
_start:
{
lean_object* v___x_4897_; lean_object* v___f_4898_; lean_object* v___f_4899_; lean_object* v___x_4900_; 
v___x_4897_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__18, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__18_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__18);
v___f_4898_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__13));
v___f_4899_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__12));
v___x_4900_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_4899_, v___f_4898_, v___x_4897_);
return v___x_4900_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__20(void){
_start:
{
lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___f_4903_; 
v___x_4901_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__15));
v___x_4902_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_4903_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4903_, 0, v___x_4902_);
lean_closure_set(v___f_4903_, 1, v___x_4901_);
return v___f_4903_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__21(void){
_start:
{
lean_object* v___f_4904_; lean_object* v___f_4905_; lean_object* v___f_4906_; 
v___f_4904_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__13));
v___f_4905_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__20, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__20_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__20);
v___f_4906_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4906_, 0, v___f_4905_);
lean_closure_set(v___f_4906_, 1, v___f_4904_);
return v___f_4906_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__23(void){
_start:
{
lean_object* v___x_4908_; lean_object* v___x_4909_; 
v___x_4908_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__22));
v___x_4909_ = l_Lean_stringToMessageData(v___x_4908_);
return v___x_4909_;
}
}
lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg(){
_start:
{
lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v_toApplicative_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4980_; 
v___x_4911_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0, &l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__0);
v___x_4912_ = l_StateRefT_x27_instMonad___redArg(v___x_4911_);
v_toApplicative_4913_ = lean_ctor_get(v___x_4912_, 0);
v_isSharedCheck_4980_ = !lean_is_exclusive(v___x_4912_);
if (v_isSharedCheck_4980_ == 0)
{
lean_object* v_unused_4981_; 
v_unused_4981_ = lean_ctor_get(v___x_4912_, 1);
lean_dec(v_unused_4981_);
v___x_4915_ = v___x_4912_;
v_isShared_4916_ = v_isSharedCheck_4980_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_toApplicative_4913_);
lean_dec(v___x_4912_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4980_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
lean_object* v_toFunctor_4917_; lean_object* v_toSeq_4918_; lean_object* v_toSeqLeft_4919_; lean_object* v_toSeqRight_4920_; lean_object* v___x_4922_; uint8_t v_isShared_4923_; uint8_t v_isSharedCheck_4978_; 
v_toFunctor_4917_ = lean_ctor_get(v_toApplicative_4913_, 0);
v_toSeq_4918_ = lean_ctor_get(v_toApplicative_4913_, 2);
v_toSeqLeft_4919_ = lean_ctor_get(v_toApplicative_4913_, 3);
v_toSeqRight_4920_ = lean_ctor_get(v_toApplicative_4913_, 4);
v_isSharedCheck_4978_ = !lean_is_exclusive(v_toApplicative_4913_);
if (v_isSharedCheck_4978_ == 0)
{
lean_object* v_unused_4979_; 
v_unused_4979_ = lean_ctor_get(v_toApplicative_4913_, 1);
lean_dec(v_unused_4979_);
v___x_4922_ = v_toApplicative_4913_;
v_isShared_4923_ = v_isSharedCheck_4978_;
goto v_resetjp_4921_;
}
else
{
lean_inc(v_toSeqRight_4920_);
lean_inc(v_toSeqLeft_4919_);
lean_inc(v_toSeq_4918_);
lean_inc(v_toFunctor_4917_);
lean_dec(v_toApplicative_4913_);
v___x_4922_ = lean_box(0);
v_isShared_4923_ = v_isSharedCheck_4978_;
goto v_resetjp_4921_;
}
v_resetjp_4921_:
{
lean_object* v___f_4924_; lean_object* v___f_4925_; lean_object* v___f_4926_; lean_object* v___f_4927_; lean_object* v___x_4928_; lean_object* v___f_4929_; lean_object* v___f_4930_; lean_object* v___f_4931_; lean_object* v___x_4933_; 
v___f_4924_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__1));
v___f_4925_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4917_);
v___f_4926_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4926_, 0, v_toFunctor_4917_);
v___f_4927_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4927_, 0, v_toFunctor_4917_);
v___x_4928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4928_, 0, v___f_4926_);
lean_ctor_set(v___x_4928_, 1, v___f_4927_);
v___f_4929_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4929_, 0, v_toSeqRight_4920_);
v___f_4930_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4930_, 0, v_toSeqLeft_4919_);
v___f_4931_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4931_, 0, v_toSeq_4918_);
if (v_isShared_4923_ == 0)
{
lean_ctor_set(v___x_4922_, 4, v___f_4929_);
lean_ctor_set(v___x_4922_, 3, v___f_4930_);
lean_ctor_set(v___x_4922_, 2, v___f_4931_);
lean_ctor_set(v___x_4922_, 1, v___f_4924_);
lean_ctor_set(v___x_4922_, 0, v___x_4928_);
v___x_4933_ = v___x_4922_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4977_; 
v_reuseFailAlloc_4977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4977_, 0, v___x_4928_);
lean_ctor_set(v_reuseFailAlloc_4977_, 1, v___f_4924_);
lean_ctor_set(v_reuseFailAlloc_4977_, 2, v___f_4931_);
lean_ctor_set(v_reuseFailAlloc_4977_, 3, v___f_4930_);
lean_ctor_set(v_reuseFailAlloc_4977_, 4, v___f_4929_);
v___x_4933_ = v_reuseFailAlloc_4977_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
lean_object* v___x_4935_; 
if (v_isShared_4916_ == 0)
{
lean_ctor_set(v___x_4915_, 1, v___f_4925_);
lean_ctor_set(v___x_4915_, 0, v___x_4933_);
v___x_4935_ = v___x_4915_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4976_; 
v_reuseFailAlloc_4976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4976_, 0, v___x_4933_);
lean_ctor_set(v_reuseFailAlloc_4976_, 1, v___f_4925_);
v___x_4935_ = v_reuseFailAlloc_4976_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
lean_object* v___x_4936_; lean_object* v_toApplicative_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4974_; 
v___x_4936_ = l_StateRefT_x27_instMonad___redArg(v___x_4935_);
v_toApplicative_4937_ = lean_ctor_get(v___x_4936_, 0);
v_isSharedCheck_4974_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_4974_ == 0)
{
lean_object* v_unused_4975_; 
v_unused_4975_ = lean_ctor_get(v___x_4936_, 1);
lean_dec(v_unused_4975_);
v___x_4939_ = v___x_4936_;
v_isShared_4940_ = v_isSharedCheck_4974_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_toApplicative_4937_);
lean_dec(v___x_4936_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_4974_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
lean_object* v_toFunctor_4941_; lean_object* v_toSeq_4942_; lean_object* v_toSeqLeft_4943_; lean_object* v_toSeqRight_4944_; lean_object* v___x_4946_; uint8_t v_isShared_4947_; uint8_t v_isSharedCheck_4972_; 
v_toFunctor_4941_ = lean_ctor_get(v_toApplicative_4937_, 0);
v_toSeq_4942_ = lean_ctor_get(v_toApplicative_4937_, 2);
v_toSeqLeft_4943_ = lean_ctor_get(v_toApplicative_4937_, 3);
v_toSeqRight_4944_ = lean_ctor_get(v_toApplicative_4937_, 4);
v_isSharedCheck_4972_ = !lean_is_exclusive(v_toApplicative_4937_);
if (v_isSharedCheck_4972_ == 0)
{
lean_object* v_unused_4973_; 
v_unused_4973_ = lean_ctor_get(v_toApplicative_4937_, 1);
lean_dec(v_unused_4973_);
v___x_4946_ = v_toApplicative_4937_;
v_isShared_4947_ = v_isSharedCheck_4972_;
goto v_resetjp_4945_;
}
else
{
lean_inc(v_toSeqRight_4944_);
lean_inc(v_toSeqLeft_4943_);
lean_inc(v_toSeq_4942_);
lean_inc(v_toFunctor_4941_);
lean_dec(v_toApplicative_4937_);
v___x_4946_ = lean_box(0);
v_isShared_4947_ = v_isSharedCheck_4972_;
goto v_resetjp_4945_;
}
v_resetjp_4945_:
{
lean_object* v___f_4948_; lean_object* v___f_4949_; lean_object* v___f_4950_; lean_object* v___f_4951_; lean_object* v___x_4952_; lean_object* v___f_4953_; lean_object* v___f_4954_; lean_object* v___f_4955_; lean_object* v___x_4957_; 
v___f_4948_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__3));
v___f_4949_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_shareCommonWithoutChecks_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4941_);
v___f_4950_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4950_, 0, v_toFunctor_4941_);
v___f_4951_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4951_, 0, v_toFunctor_4941_);
v___x_4952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4952_, 0, v___f_4950_);
lean_ctor_set(v___x_4952_, 1, v___f_4951_);
v___f_4953_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4953_, 0, v_toSeqRight_4944_);
v___f_4954_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4954_, 0, v_toSeqLeft_4943_);
v___f_4955_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4955_, 0, v_toSeq_4942_);
if (v_isShared_4947_ == 0)
{
lean_ctor_set(v___x_4946_, 4, v___f_4953_);
lean_ctor_set(v___x_4946_, 3, v___f_4954_);
lean_ctor_set(v___x_4946_, 2, v___f_4955_);
lean_ctor_set(v___x_4946_, 1, v___f_4948_);
lean_ctor_set(v___x_4946_, 0, v___x_4952_);
v___x_4957_ = v___x_4946_;
goto v_reusejp_4956_;
}
else
{
lean_object* v_reuseFailAlloc_4971_; 
v_reuseFailAlloc_4971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4971_, 0, v___x_4952_);
lean_ctor_set(v_reuseFailAlloc_4971_, 1, v___f_4948_);
lean_ctor_set(v_reuseFailAlloc_4971_, 2, v___f_4955_);
lean_ctor_set(v_reuseFailAlloc_4971_, 3, v___f_4954_);
lean_ctor_set(v_reuseFailAlloc_4971_, 4, v___f_4953_);
v___x_4957_ = v_reuseFailAlloc_4971_;
goto v_reusejp_4956_;
}
v_reusejp_4956_:
{
lean_object* v___x_4959_; 
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 1, v___f_4949_);
lean_ctor_set(v___x_4939_, 0, v___x_4957_);
v___x_4959_ = v___x_4939_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4970_; 
v_reuseFailAlloc_4970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4970_, 0, v___x_4957_);
lean_ctor_set(v_reuseFailAlloc_4970_, 1, v___f_4949_);
v___x_4959_ = v_reuseFailAlloc_4970_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v_toMonadRef_4964_; lean_object* v___f_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; 
v___x_4960_ = l_StateRefT_x27_instMonad___redArg(v___x_4959_);
v___x_4961_ = l_ReaderT_instMonad___redArg(v___x_4960_);
v___x_4962_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__11, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__11_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__11);
v___x_4963_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__19, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__19_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__19);
v_toMonadRef_4964_ = lean_ctor_get(v___x_4963_, 0);
v___f_4965_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__21, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__21_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__21);
lean_inc_ref(v___x_4961_);
v___x_4966_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_4965_, v___x_4961_);
lean_inc_ref(v_toMonadRef_4964_);
v___x_4967_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4967_, 0, v___x_4962_);
lean_ctor_set(v___x_4967_, 1, v_toMonadRef_4964_);
lean_ctor_set(v___x_4967_, 2, v___x_4966_);
v___x_4968_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__23, &l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__23_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___redArg___closed__23);
v___x_4969_ = l_Lean_throwError___redArg(v___x_4961_, v___x_4967_, v___x_4968_);
return v___x_4969_;
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
LEAN_EXPORT void l_Lean_Meta_Sym_instInhabitedSymM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4982_;
v_res_4982_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
stack->m_obj
 = v_res_4982_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg___boxed(lean_object* v___dummy_4983_){
_start:
{
lean_object* v_res_4984_; 
v_res_4984_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v_res_4984_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0(void){
_start:
{
lean_object* v___x_4985_; 
v___x_4985_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_4985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object* v_00_u03b1_4986_){
_start:
{
lean_object* v___x_4987_; 
v___x_4987_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__0, &l_Lean_Meta_Sym_instInhabitedSymM___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0);
return v___x_4987_;
}
}
lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(lean_object* v_ext_4988_, lean_object* v_extensions_4989_){
_start:
{
lean_object* v_id_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
v_id_4991_ = lean_ctor_get(v_ext_4988_, 0);
v___x_4992_ = l_Lean_Meta_Sym_instInhabitedSymExtensionState;
v___x_4993_ = lean_array_get_borrowed(v___x_4992_, v_extensions_4989_, v_id_4991_);
lean_inc(v___x_4993_);
v___x_4994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4994_, 0, v___x_4993_);
return v___x_4994_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_4988_ = stack[0].m_obj;
lean_object* v_extensions_4989_ = stack[1].m_obj;
lean_object* v_res_4995_;
v_res_4995_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_4988_, v_extensions_4989_);
stack->m_obj
 = v_res_4995_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg___boxed(lean_object* v_ext_4996_, lean_object* v_extensions_4997_, lean_object* v_a_4998_){
_start:
{
lean_object* v_res_4999_; 
v_res_4999_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_4996_, v_extensions_4997_);
lean_dec_ref(v_extensions_4997_);
lean_dec_ref(v_ext_4996_);
return v_res_4999_;
}
}
lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(lean_object* v_00_u03c3_5000_, lean_object* v_ext_5001_, lean_object* v_extensions_5002_){
_start:
{
lean_object* v___x_5004_; 
v___x_5004_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_5001_, v_extensions_5002_);
return v___x_5004_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_5001_ = stack[1].m_obj;
lean_object* v_extensions_5002_ = stack[2].m_obj;
lean_object* v_res_5005_;
v_res_5005_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(lean_box(0), v_ext_5001_, v_extensions_5002_);
stack->m_obj
 = v_res_5005_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___boxed(lean_object* v_00_u03c3_5006_, lean_object* v_ext_5007_, lean_object* v_extensions_5008_, lean_object* v_a_5009_){
_start:
{
lean_object* v_res_5010_; 
v_res_5010_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(v_00_u03c3_5006_, v_ext_5007_, v_extensions_5008_);
lean_dec_ref(v_extensions_5008_);
lean_dec_ref(v_ext_5007_);
return v_res_5010_;
}
}
lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg(lean_object* v_ext_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_){
_start:
{
lean_object* v___x_5015_; lean_object* v_extensions_5016_; lean_object* v_ref_5017_; lean_object* v___x_5018_; 
v___x_5015_ = lean_st_ref_get(v_a_5012_);
v_extensions_5016_ = lean_ctor_get(v___x_5015_, 8);
lean_inc_ref(v_extensions_5016_);
lean_dec(v___x_5015_);
v_ref_5017_ = lean_ctor_get(v_a_5013_, 2);
v___x_5018_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_5011_, v_extensions_5016_);
lean_dec_ref(v_extensions_5016_);
if (lean_obj_tag(v___x_5018_) == 0)
{
lean_object* v_a_5019_; lean_object* v___x_5021_; uint8_t v_isShared_5022_; uint8_t v_isSharedCheck_5026_; 
v_a_5019_ = lean_ctor_get(v___x_5018_, 0);
v_isSharedCheck_5026_ = !lean_is_exclusive(v___x_5018_);
if (v_isSharedCheck_5026_ == 0)
{
v___x_5021_ = v___x_5018_;
v_isShared_5022_ = v_isSharedCheck_5026_;
goto v_resetjp_5020_;
}
else
{
lean_inc(v_a_5019_);
lean_dec(v___x_5018_);
v___x_5021_ = lean_box(0);
v_isShared_5022_ = v_isSharedCheck_5026_;
goto v_resetjp_5020_;
}
v_resetjp_5020_:
{
lean_object* v___x_5024_; 
if (v_isShared_5022_ == 0)
{
v___x_5024_ = v___x_5021_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v_a_5019_);
v___x_5024_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
return v___x_5024_;
}
}
}
else
{
lean_object* v_a_5027_; lean_object* v___x_5029_; uint8_t v_isShared_5030_; uint8_t v_isSharedCheck_5038_; 
v_a_5027_ = lean_ctor_get(v___x_5018_, 0);
v_isSharedCheck_5038_ = !lean_is_exclusive(v___x_5018_);
if (v_isSharedCheck_5038_ == 0)
{
v___x_5029_ = v___x_5018_;
v_isShared_5030_ = v_isSharedCheck_5038_;
goto v_resetjp_5028_;
}
else
{
lean_inc(v_a_5027_);
lean_dec(v___x_5018_);
v___x_5029_ = lean_box(0);
v_isShared_5030_ = v_isSharedCheck_5038_;
goto v_resetjp_5028_;
}
v_resetjp_5028_:
{
lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5036_; 
v___x_5031_ = lean_io_error_to_string(v_a_5027_);
v___x_5032_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5032_, 0, v___x_5031_);
v___x_5033_ = l_Lean_MessageData_ofFormat(v___x_5032_);
lean_inc(v_ref_5017_);
v___x_5034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5034_, 0, v_ref_5017_);
lean_ctor_set(v___x_5034_, 1, v___x_5033_);
if (v_isShared_5030_ == 0)
{
lean_ctor_set(v___x_5029_, 0, v___x_5034_);
v___x_5036_ = v___x_5029_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_SymExtension_getState___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_5011_ = stack[0].m_obj;
lean_object* v_a_5012_ = stack[1].m_obj;
lean_object* v_a_5013_ = stack[2].m_obj;
lean_object* v_res_5039_;
v_res_5039_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_5011_, v_a_5012_, v_a_5013_);
stack->m_obj
 = v_res_5039_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg___boxed(lean_object* v_ext_5040_, lean_object* v_a_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_){
_start:
{
lean_object* v_res_5044_; 
v_res_5044_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_5040_, v_a_5041_, v_a_5042_);
lean_dec_ref(v_a_5042_);
lean_dec(v_a_5041_);
lean_dec_ref(v_ext_5040_);
return v_res_5044_;
}
}
lean_object* l_Lean_Meta_Sym_SymExtension_getState(lean_object* v_00_u03c3_5045_, lean_object* v_ext_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_){
_start:
{
lean_object* v___x_5054_; 
v___x_5054_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_5046_, v_a_5048_, v_a_5051_);
return v___x_5054_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_SymExtension_getState_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_5046_ = stack[1].m_obj;
lean_object* v_a_5047_ = stack[2].m_obj;
lean_object* v_a_5048_ = stack[3].m_obj;
lean_object* v_a_5049_ = stack[4].m_obj;
lean_object* v_a_5050_ = stack[5].m_obj;
lean_object* v_a_5051_ = stack[6].m_obj;
lean_object* v_a_5052_ = stack[7].m_obj;
lean_object* v_res_5055_;
v_res_5055_ = l_Lean_Meta_Sym_SymExtension_getState(lean_box(0), v_ext_5046_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_, v_a_5051_, v_a_5052_);
stack->m_obj
 = v_res_5055_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___boxed(lean_object* v_00_u03c3_5056_, lean_object* v_ext_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_){
_start:
{
lean_object* v_res_5065_; 
v_res_5065_ = l_Lean_Meta_Sym_SymExtension_getState(v_00_u03c3_5056_, v_ext_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
lean_dec(v_a_5063_);
lean_dec_ref(v_a_5062_);
lean_dec(v_a_5061_);
lean_dec_ref(v_a_5060_);
lean_dec(v_a_5059_);
lean_dec_ref(v_a_5058_);
lean_dec_ref(v_ext_5057_);
return v_res_5065_;
}
}
lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(lean_object* v_ext_5066_, lean_object* v_f_5067_, lean_object* v_a_5068_){
_start:
{
lean_object* v___x_5070_; lean_object* v_share_5071_; lean_object* v_maxFVar_5072_; lean_object* v_proofInstInfo_5073_; lean_object* v_proofInstInfoFVar_5074_; lean_object* v_inferType_5075_; lean_object* v_getLevel_5076_; lean_object* v_congrInfo_5077_; lean_object* v_defEqI_5078_; lean_object* v_extensions_5079_; lean_object* v_issues_5080_; lean_object* v_canon_5081_; lean_object* v_instanceOverrides_5082_; uint8_t v_debug_5083_; lean_object* v___x_5085_; uint8_t v_isShared_5086_; uint8_t v_isSharedCheck_5102_; 
v___x_5070_ = lean_st_ref_take(v_a_5068_);
v_share_5071_ = lean_ctor_get(v___x_5070_, 0);
v_maxFVar_5072_ = lean_ctor_get(v___x_5070_, 1);
v_proofInstInfo_5073_ = lean_ctor_get(v___x_5070_, 2);
v_proofInstInfoFVar_5074_ = lean_ctor_get(v___x_5070_, 3);
v_inferType_5075_ = lean_ctor_get(v___x_5070_, 4);
v_getLevel_5076_ = lean_ctor_get(v___x_5070_, 5);
v_congrInfo_5077_ = lean_ctor_get(v___x_5070_, 6);
v_defEqI_5078_ = lean_ctor_get(v___x_5070_, 7);
v_extensions_5079_ = lean_ctor_get(v___x_5070_, 8);
v_issues_5080_ = lean_ctor_get(v___x_5070_, 9);
v_canon_5081_ = lean_ctor_get(v___x_5070_, 10);
v_instanceOverrides_5082_ = lean_ctor_get(v___x_5070_, 11);
v_debug_5083_ = lean_ctor_get_uint8(v___x_5070_, sizeof(void*)*12);
v_isSharedCheck_5102_ = !lean_is_exclusive(v___x_5070_);
if (v_isSharedCheck_5102_ == 0)
{
v___x_5085_ = v___x_5070_;
v_isShared_5086_ = v_isSharedCheck_5102_;
goto v_resetjp_5084_;
}
else
{
lean_inc(v_instanceOverrides_5082_);
lean_inc(v_canon_5081_);
lean_inc(v_issues_5080_);
lean_inc(v_extensions_5079_);
lean_inc(v_defEqI_5078_);
lean_inc(v_congrInfo_5077_);
lean_inc(v_getLevel_5076_);
lean_inc(v_inferType_5075_);
lean_inc(v_proofInstInfoFVar_5074_);
lean_inc(v_proofInstInfo_5073_);
lean_inc(v_maxFVar_5072_);
lean_inc(v_share_5071_);
lean_dec(v___x_5070_);
v___x_5085_ = lean_box(0);
v_isShared_5086_ = v_isSharedCheck_5102_;
goto v_resetjp_5084_;
}
v_resetjp_5084_:
{
lean_object* v_id_5087_; lean_object* v___x_5088_; lean_object* v___y_5090_; lean_object* v___x_5096_; uint8_t v___x_5097_; 
v_id_5087_ = lean_ctor_get(v_ext_5066_, 0);
v___x_5088_ = lean_box(0);
v___x_5096_ = lean_array_get_size(v_extensions_5079_);
v___x_5097_ = lean_nat_dec_lt(v_id_5087_, v___x_5096_);
if (v___x_5097_ == 0)
{
lean_dec(v_f_5067_);
v___y_5090_ = v_extensions_5079_;
goto v___jp_5089_;
}
else
{
lean_object* v_v_5098_; lean_object* v_xs_x27_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; 
v_v_5098_ = lean_array_fget(v_extensions_5079_, v_id_5087_);
v_xs_x27_5099_ = lean_array_fset(v_extensions_5079_, v_id_5087_, v___x_5088_);
v___x_5100_ = lean_apply_1(v_f_5067_, v_v_5098_);
v___x_5101_ = lean_array_fset(v_xs_x27_5099_, v_id_5087_, v___x_5100_);
v___y_5090_ = v___x_5101_;
goto v___jp_5089_;
}
v___jp_5089_:
{
lean_object* v___x_5092_; 
if (v_isShared_5086_ == 0)
{
lean_ctor_set(v___x_5085_, 8, v___y_5090_);
v___x_5092_ = v___x_5085_;
goto v_reusejp_5091_;
}
else
{
lean_object* v_reuseFailAlloc_5095_; 
v_reuseFailAlloc_5095_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_5095_, 0, v_share_5071_);
lean_ctor_set(v_reuseFailAlloc_5095_, 1, v_maxFVar_5072_);
lean_ctor_set(v_reuseFailAlloc_5095_, 2, v_proofInstInfo_5073_);
lean_ctor_set(v_reuseFailAlloc_5095_, 3, v_proofInstInfoFVar_5074_);
lean_ctor_set(v_reuseFailAlloc_5095_, 4, v_inferType_5075_);
lean_ctor_set(v_reuseFailAlloc_5095_, 5, v_getLevel_5076_);
lean_ctor_set(v_reuseFailAlloc_5095_, 6, v_congrInfo_5077_);
lean_ctor_set(v_reuseFailAlloc_5095_, 7, v_defEqI_5078_);
lean_ctor_set(v_reuseFailAlloc_5095_, 8, v___y_5090_);
lean_ctor_set(v_reuseFailAlloc_5095_, 9, v_issues_5080_);
lean_ctor_set(v_reuseFailAlloc_5095_, 10, v_canon_5081_);
lean_ctor_set(v_reuseFailAlloc_5095_, 11, v_instanceOverrides_5082_);
lean_ctor_set_uint8(v_reuseFailAlloc_5095_, sizeof(void*)*12, v_debug_5083_);
v___x_5092_ = v_reuseFailAlloc_5095_;
goto v_reusejp_5091_;
}
v_reusejp_5091_:
{
lean_object* v___x_5093_; lean_object* v___x_5094_; 
v___x_5093_ = lean_st_ref_put(v_a_5068_, v___x_5092_);
v___x_5094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5094_, 0, v___x_5088_);
return v___x_5094_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_5066_ = stack[0].m_obj;
lean_object* v_f_5067_ = stack[1].m_obj;
lean_object* v_a_5068_ = stack[2].m_obj;
lean_object* v_res_5103_;
v_res_5103_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_5066_, v_f_5067_, v_a_5068_);
stack->m_obj
 = v_res_5103_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg___boxed(lean_object* v_ext_5104_, lean_object* v_f_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_){
_start:
{
lean_object* v_res_5108_; 
v_res_5108_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_5104_, v_f_5105_, v_a_5106_);
lean_dec(v_a_5106_);
lean_dec_ref(v_ext_5104_);
return v_res_5108_;
}
}
lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(lean_object* v_00_u03c3_5109_, lean_object* v_ext_5110_, lean_object* v_f_5111_, lean_object* v_a_5112_, lean_object* v_a_5113_, lean_object* v_a_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_){
_start:
{
lean_object* v___x_5119_; 
v___x_5119_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_5110_, v_f_5111_, v_a_5113_);
return v___x_5119_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_5110_ = stack[1].m_obj;
lean_object* v_f_5111_ = stack[2].m_obj;
lean_object* v_a_5112_ = stack[3].m_obj;
lean_object* v_a_5113_ = stack[4].m_obj;
lean_object* v_a_5114_ = stack[5].m_obj;
lean_object* v_a_5115_ = stack[6].m_obj;
lean_object* v_a_5116_ = stack[7].m_obj;
lean_object* v_a_5117_ = stack[8].m_obj;
lean_object* v_res_5120_;
v_res_5120_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(lean_box(0), v_ext_5110_, v_f_5111_, v_a_5112_, v_a_5113_, v_a_5114_, v_a_5115_, v_a_5116_, v_a_5117_);
stack->m_obj
 = v_res_5120_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___boxed(lean_object* v_00_u03c3_5121_, lean_object* v_ext_5122_, lean_object* v_f_5123_, lean_object* v_a_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_, lean_object* v_a_5128_, lean_object* v_a_5129_, lean_object* v_a_5130_){
_start:
{
lean_object* v_res_5131_; 
v_res_5131_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(v_00_u03c3_5121_, v_ext_5122_, v_f_5123_, v_a_5124_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_, v_a_5129_);
lean_dec(v_a_5129_);
lean_dec_ref(v_a_5128_);
lean_dec(v_a_5127_);
lean_dec_ref(v_a_5126_);
lean_dec(v_a_5125_);
lean_dec_ref(v_a_5124_);
lean_dec_ref(v_ext_5122_);
return v_res_5131_;
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
