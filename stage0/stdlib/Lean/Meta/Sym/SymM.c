// Lean compiler output
// Module: Lean.Meta.Sym.SymM
// Imports: public import Lean.Meta.Sym.AlphaShareCommon public import Lean.Meta.CongrTheorems
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
extern lean_object* l_Lean_Int_mkType;
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_initializing();
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_instInhabitedConfig_default;
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_instInhabitedConfig;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_SymM_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Sym_SymM_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__2;
static lean_once_cell_t l_Lean_Meta_Sym_SymM_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__3;
static lean_once_cell_t l_Lean_Meta_Sym_SymM_run___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SymM_run___redArg___closed__4;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Sym_reportIssue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Sym_reportIssue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_reportIssue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "issue"};
static const lean_object* l_Lean_Meta_Sym_reportIssue___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_reportIssue___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_reportIssue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_reportIssue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 190, 118, 187, 186, 110, 108, 236)}};
static const lean_object* l_Lean_Meta_Sym_reportIssue___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_reportIssue___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_reportIssue___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_reportIssue___closed__2;
static const lean_string_object l_Lean_Meta_Sym_reportIssue___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Sym_reportIssue___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_reportIssue___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_reportIssue___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_reportIssue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Sym_reportIssue___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_reportIssue___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Sym_reportIssue___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_reportIssue___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___closed__2_value;
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___closed__3_value;
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___closed__4_value;
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___closed__5_value;
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
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__12;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__13;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__14;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__15;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__16;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__17;
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymM___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__18 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___closed__18_value;
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymM___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__19 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___closed__19_value;
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymM___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__20 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___closed__20_value;
static const lean_closure_object l_Lean_Meta_Sym_instInhabitedSymM___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__21 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___closed__21_value;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__22;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__23;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__24;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__25;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__26;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__27;
static const lean_string_object l_Lean_Meta_Sym_instInhabitedSymM___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "<SymM default value>"};
static const lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__28 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedSymM___closed__28_value;
static lean_once_cell_t l_Lean_Meta_Sym_instInhabitedSymM___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instInhabitedSymM___closed__29;
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
static uint8_t _init_l_Lean_Meta_Sym_instInhabitedConfig_default(void){
_start:
{
uint8_t v___x_323_; 
v___x_323_ = 1;
return v___x_323_;
}
}
static uint8_t _init_l_Lean_Meta_Sym_instInhabitedConfig(void){
_start:
{
uint8_t v___x_324_; 
v___x_324_ = 1;
return v___x_324_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = lean_box(0);
v___x_329_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1));
v___x_330_ = l_Lean_mkConst(v___x_329_, v___x_328_);
return v___x_330_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_334_ = lean_box(0);
v___x_335_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4));
v___x_336_ = l_Lean_mkConst(v___x_335_, v___x_334_);
return v___x_336_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_342_ = lean_box(0);
v___x_343_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8));
v___x_344_ = l_Lean_mkConst(v___x_343_, v___x_342_);
return v___x_344_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_349_ = lean_box(0);
v___x_350_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11));
v___x_351_ = l_Lean_mkConst(v___x_350_, v___x_349_);
return v___x_351_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = l_Lean_mkNatLit(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = lean_box(0);
v___x_360_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16));
v___x_361_ = l_Lean_mkConst(v___x_360_, v___x_359_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(lean_object* v_a_362_){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v_fst_365_; lean_object* v_snd_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v_fst_369_; lean_object* v_snd_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v_fst_373_; lean_object* v_snd_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v_fst_377_; lean_object* v_snd_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v_fst_381_; lean_object* v_snd_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v_fst_385_; lean_object* v_snd_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v_fst_389_; lean_object* v_snd_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_398_; 
v___x_363_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2);
v___x_364_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_363_, v_a_362_);
v_fst_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_fst_365_);
v_snd_366_ = lean_ctor_get(v___x_364_, 1);
lean_inc(v_snd_366_);
lean_dec_ref(v___x_364_);
v___x_367_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5);
v___x_368_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_367_, v_snd_366_);
v_fst_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_fst_369_);
v_snd_370_ = lean_ctor_get(v___x_368_, 1);
lean_inc(v_snd_370_);
lean_dec_ref(v___x_368_);
v___x_371_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9);
v___x_372_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_371_, v_snd_370_);
v_fst_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_fst_373_);
v_snd_374_ = lean_ctor_get(v___x_372_, 1);
lean_inc(v_snd_374_);
lean_dec_ref(v___x_372_);
v___x_375_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12);
v___x_376_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_375_, v_snd_374_);
v_fst_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_fst_377_);
v_snd_378_ = lean_ctor_get(v___x_376_, 1);
lean_inc(v_snd_378_);
lean_dec_ref(v___x_376_);
v___x_379_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13);
v___x_380_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_379_, v_snd_378_);
v_fst_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_fst_381_);
v_snd_382_ = lean_ctor_get(v___x_380_, 1);
lean_inc(v_snd_382_);
lean_dec_ref(v___x_380_);
v___x_383_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17);
v___x_384_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_383_, v_snd_382_);
v_fst_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_fst_385_);
v_snd_386_ = lean_ctor_get(v___x_384_, 1);
lean_inc(v_snd_386_);
lean_dec_ref(v___x_384_);
v___x_387_ = l_Lean_Int_mkType;
v___x_388_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_387_, v_snd_386_);
v_fst_389_ = lean_ctor_get(v___x_388_, 0);
v_snd_390_ = lean_ctor_get(v___x_388_, 1);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_398_ == 0)
{
v___x_392_ = v___x_388_;
v_isShared_393_ = v_isSharedCheck_398_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_snd_390_);
lean_inc(v_fst_389_);
lean_dec(v___x_388_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_398_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_394_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_394_, 0, v_fst_369_);
lean_ctor_set(v___x_394_, 1, v_fst_365_);
lean_ctor_set(v___x_394_, 2, v_fst_381_);
lean_ctor_set(v___x_394_, 3, v_fst_377_);
lean_ctor_set(v___x_394_, 4, v_fst_373_);
lean_ctor_set(v___x_394_, 5, v_fst_385_);
lean_ctor_set(v___x_394_, 6, v_fst_389_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v___x_394_);
v___x_396_ = v___x_392_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_snd_390_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__0(void){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_399_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__1(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__0);
v___x_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0(lean_object* v_00_u03b2_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__1);
return v___x_403_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__1(lean_object* v_opts_404_, lean_object* v_opt_405_){
_start:
{
lean_object* v_name_406_; lean_object* v_defValue_407_; lean_object* v_map_408_; lean_object* v___x_409_; 
v_name_406_ = lean_ctor_get(v_opt_405_, 0);
v_defValue_407_ = lean_ctor_get(v_opt_405_, 1);
v_map_408_ = lean_ctor_get(v_opts_404_, 0);
v___x_409_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_408_, v_name_406_);
if (lean_obj_tag(v___x_409_) == 0)
{
uint8_t v___x_410_; 
v___x_410_ = lean_unbox(v_defValue_407_);
return v___x_410_;
}
else
{
lean_object* v_val_411_; 
v_val_411_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_val_411_);
lean_dec_ref_known(v___x_409_, 1);
if (lean_obj_tag(v_val_411_) == 1)
{
uint8_t v_v_412_; 
v_v_412_ = lean_ctor_get_uint8(v_val_411_, 0);
lean_dec_ref_known(v_val_411_, 0);
return v_v_412_;
}
else
{
uint8_t v___x_413_; 
lean_dec(v_val_411_);
v___x_413_ = lean_unbox(v_defValue_407_);
return v___x_413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__1___boxed(lean_object* v_opts_414_, lean_object* v_opt_415_){
_start:
{
uint8_t v_res_416_; lean_object* v_r_417_; 
v_res_416_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__1(v_opts_414_, v_opt_415_);
lean_dec_ref(v_opt_415_);
lean_dec_ref(v_opts_414_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0(lean_box(0));
return v___x_418_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_419_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__1, &l_Lean_Meta_Sym_SymM_run___redArg___closed__1_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_422_ = lean_box(0);
v___x_423_ = lean_unsigned_to_nat(16u);
v___x_424_ = lean_mk_array(v___x_423_, v___x_422_);
return v___x_424_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__4(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_425_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__3, &l_Lean_Meta_Sym_SymM_run___redArg___closed__3_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__3);
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
lean_ctor_set(v___x_427_, 1, v___x_425_);
return v___x_427_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__5(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__4, &l_Lean_Meta_Sym_SymM_run___redArg___closed__4_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__4);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object* v_x_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v_fst_438_; lean_object* v_snd_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_480_; 
v___x_436_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__0, &l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0);
v___x_437_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(v___x_436_);
v_fst_438_ = lean_ctor_get(v___x_437_, 0);
v_snd_439_ = lean_ctor_get(v___x_437_, 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_480_ == 0)
{
v___x_441_ = v___x_437_;
v_isShared_442_ = v_isSharedCheck_480_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_snd_439_);
lean_inc(v_fst_438_);
lean_dec(v___x_437_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_480_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v_options_445_; lean_object* v___x_446_; uint8_t v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
lean_del_object(v___x_441_);
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
lean_dec_ref_known(v___x_443_, 1);
v_options_445_ = lean_ctor_get(v_a_433_, 2);
v___x_446_ = l_Lean_Meta_Sym_sym_debug;
v___x_447_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__1(v_options_445_, v___x_446_);
v___x_448_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__2, &l_Lean_Meta_Sym_SymM_run___redArg___closed__2_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__2);
v___x_449_ = lean_box(0);
v___x_450_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__5, &l_Lean_Meta_Sym_SymM_run___redArg___closed__5_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__5);
v___x_451_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_451_, 0, v_snd_439_);
lean_ctor_set(v___x_451_, 1, v___x_448_);
lean_ctor_set(v___x_451_, 2, v___x_448_);
lean_ctor_set(v___x_451_, 3, v___x_448_);
lean_ctor_set(v___x_451_, 4, v___x_448_);
lean_ctor_set(v___x_451_, 5, v___x_448_);
lean_ctor_set(v___x_451_, 6, v___x_448_);
lean_ctor_set(v___x_451_, 7, v_a_444_);
lean_ctor_set(v___x_451_, 8, v___x_449_);
lean_ctor_set(v___x_451_, 9, v___x_450_);
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*10, v___x_447_);
v___x_452_ = lean_st_mk_ref(v___x_451_);
v___x_453_ = 1;
v___x_454_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_454_, 0, v_fst_438_);
lean_ctor_set_uint8(v___x_454_, sizeof(void*)*1, v___x_453_);
lean_inc(v_a_434_);
lean_inc_ref(v_a_433_);
lean_inc(v_a_432_);
lean_inc_ref(v_a_431_);
lean_inc(v___x_452_);
v___x_455_ = lean_apply_7(v_x_430_, v___x_454_, v___x_452_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, lean_box(0));
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_464_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_464_ == 0)
{
v___x_458_ = v___x_455_;
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_460_ = lean_st_ref_get(v___x_452_);
lean_dec(v___x_452_);
lean_dec(v___x_460_);
if (v_isShared_459_ == 0)
{
v___x_462_ = v___x_458_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_456_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
else
{
lean_dec(v___x_452_);
return v___x_455_;
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_479_; 
lean_dec(v_snd_439_);
lean_dec(v_fst_438_);
lean_dec_ref(v_x_430_);
v_a_465_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_479_ == 0)
{
v___x_467_ = v___x_443_;
v_isShared_468_ = v_isSharedCheck_479_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_443_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_479_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v_ref_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
v_ref_469_ = lean_ctor_get(v_a_433_, 5);
v___x_470_ = lean_io_error_to_string(v_a_465_);
v___x_471_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
v___x_472_ = l_Lean_MessageData_ofFormat(v___x_471_);
lean_inc(v_ref_469_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 1, v___x_472_);
lean_ctor_set(v___x_441_, 0, v_ref_469_);
v___x_474_ = v___x_441_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_ref_469_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v___x_472_);
v___x_474_ = v_reuseFailAlloc_478_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_476_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 0, v___x_474_);
v___x_476_ = v___x_467_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___redArg___boxed(lean_object* v_x_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_);
lean_dec(v_a_485_);
lean_dec_ref(v_a_484_);
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run(lean_object* v_00_u03b1_488_, lean_object* v_x_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_Meta_Sym_SymM_run___redArg(v_x_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymM_run___boxed(lean_object* v_00_u03b1_496_, lean_object* v_x_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_Meta_Sym_SymM_run(v_00_u03b1_496_, v_x_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
lean_dec(v_a_501_);
lean_dec_ref(v_a_500_);
lean_dec(v_a_499_);
lean_dec_ref(v_a_498_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg(lean_object* v_a_504_){
_start:
{
lean_object* v_sharedExprs_506_; lean_object* v___x_507_; 
v_sharedExprs_506_ = lean_ctor_get(v_a_504_, 0);
lean_inc_ref(v_sharedExprs_506_);
v___x_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_507_, 0, v_sharedExprs_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___redArg___boxed(lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_508_);
lean_dec_ref(v_a_508_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs(lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_511_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getSharedExprs___boxed(lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_Meta_Sym_getSharedExprs(v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object* v_a_527_){
_start:
{
lean_object* v___x_529_; lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_538_; 
v___x_529_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_527_);
v_a_530_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_538_ == 0)
{
v___x_532_ = v___x_529_;
v_isShared_533_ = v_isSharedCheck_538_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_538_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v_trueExpr_534_; lean_object* v___x_536_; 
v_trueExpr_534_ = lean_ctor_get(v_a_530_, 0);
lean_inc_ref(v_trueExpr_534_);
lean_dec(v_a_530_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v_trueExpr_534_);
v___x_536_ = v___x_532_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_trueExpr_534_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg___boxed(lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_539_);
lean_dec_ref(v_a_539_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr(lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_542_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getTrueExpr___boxed(lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_Meta_Sym_getTrueExpr(v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object* v_e_558_, lean_object* v_a_559_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_559_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_571_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_571_ == 0)
{
v___x_564_ = v___x_561_;
v_isShared_565_ = v_isSharedCheck_571_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_561_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_571_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
uint8_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_566_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_558_, v_a_562_);
lean_dec(v_a_562_);
v___x_567_ = lean_box(v___x_566_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_567_);
v___x_569_ = v___x_564_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
else
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
v_a_572_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v___x_561_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_561_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg___boxed(lean_object* v_e_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_580_, v_a_581_);
lean_dec_ref(v_a_581_);
lean_dec_ref(v_e_580_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr(lean_object* v_e_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_584_, v_a_585_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isTrueExpr___boxed(lean_object* v_e_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_Meta_Sym_isTrueExpr(v_e_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
lean_dec_ref(v_e_593_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object* v_a_602_){
_start:
{
lean_object* v___x_604_; lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_613_; 
v___x_604_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_602_);
v_a_605_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_613_ == 0)
{
v___x_607_ = v___x_604_;
v_isShared_608_ = v_isSharedCheck_613_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_613_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v_falseExpr_609_; lean_object* v___x_611_; 
v_falseExpr_609_ = lean_ctor_get(v_a_605_, 1);
lean_inc_ref(v_falseExpr_609_);
lean_dec(v_a_605_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v_falseExpr_609_);
v___x_611_ = v___x_607_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_falseExpr_609_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg___boxed(lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_614_);
lean_dec_ref(v_a_614_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr(lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_617_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFalseExpr___boxed(lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_Meta_Sym_getFalseExpr(v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object* v_e_633_, lean_object* v_a_634_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_634_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_646_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_646_ == 0)
{
v___x_639_ = v___x_636_;
v_isShared_640_ = v_isSharedCheck_646_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_636_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_646_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
uint8_t v___x_641_; lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_641_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_633_, v_a_637_);
lean_dec(v_a_637_);
v___x_642_ = lean_box(v___x_641_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_642_);
v___x_644_ = v___x_639_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_642_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
v_a_647_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_636_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_636_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg___boxed(lean_object* v_e_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_655_, v_a_656_);
lean_dec_ref(v_a_656_);
lean_dec_ref(v_e_655_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr(lean_object* v_e_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_659_, v_a_660_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isFalseExpr___boxed(lean_object* v_e_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_Meta_Sym_isFalseExpr(v_e_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec(v_a_672_);
lean_dec_ref(v_a_671_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
lean_dec_ref(v_e_668_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object* v_a_677_){
_start:
{
lean_object* v___x_679_; lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_688_; 
v___x_679_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_677_);
v_a_680_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_688_ == 0)
{
v___x_682_ = v___x_679_;
v_isShared_683_ = v_isSharedCheck_688_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_679_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_688_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v_btrueExpr_684_; lean_object* v___x_686_; 
v_btrueExpr_684_ = lean_ctor_get(v_a_680_, 3);
lean_inc_ref(v_btrueExpr_684_);
lean_dec(v_a_680_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v_btrueExpr_684_);
v___x_686_ = v___x_682_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_btrueExpr_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg___boxed(lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_689_);
lean_dec_ref(v_a_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr(lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_692_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___boxed(lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_Meta_Sym_getBoolTrueExpr(v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
lean_dec(v_a_701_);
lean_dec_ref(v_a_700_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg(lean_object* v_e_708_, lean_object* v_a_709_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_709_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_721_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_721_ == 0)
{
v___x_714_ = v___x_711_;
v_isShared_715_ = v_isSharedCheck_721_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_711_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_721_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
uint8_t v___x_716_; lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_716_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_708_, v_a_712_);
lean_dec(v_a_712_);
v___x_717_ = lean_box(v___x_716_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_717_);
v___x_719_ = v___x_714_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
v_a_722_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_711_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_711_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg___boxed(lean_object* v_e_730_, lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_730_, v_a_731_);
lean_dec_ref(v_a_731_);
lean_dec_ref(v_e_730_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr(lean_object* v_e_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_734_, v_a_735_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___boxed(lean_object* v_e_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_Meta_Sym_isBoolTrueExpr(v_e_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
lean_dec_ref(v_e_743_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object* v_a_752_){
_start:
{
lean_object* v___x_754_; lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_763_; 
v___x_754_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_752_);
v_a_755_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_763_ == 0)
{
v___x_757_ = v___x_754_;
v_isShared_758_ = v_isSharedCheck_763_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_754_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_763_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v_bfalseExpr_759_; lean_object* v___x_761_; 
v_bfalseExpr_759_ = lean_ctor_get(v_a_755_, 4);
lean_inc_ref(v_bfalseExpr_759_);
lean_dec(v_a_755_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v_bfalseExpr_759_);
v___x_761_ = v___x_757_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_bfalseExpr_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg___boxed(lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_764_);
lean_dec_ref(v_a_764_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr(lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_767_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___boxed(lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Meta_Sym_getBoolFalseExpr(v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg(lean_object* v_e_783_, lean_object* v_a_784_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_784_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_796_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_796_ == 0)
{
v___x_789_ = v___x_786_;
v_isShared_790_ = v_isSharedCheck_796_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_786_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_796_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
uint8_t v___x_791_; lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_791_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_783_, v_a_787_);
lean_dec(v_a_787_);
v___x_792_ = lean_box(v___x_791_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_792_);
v___x_794_ = v___x_789_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
v_a_797_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_786_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_786_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg___boxed(lean_object* v_e_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_805_, v_a_806_);
lean_dec_ref(v_a_806_);
lean_dec_ref(v_e_805_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr(lean_object* v_e_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_809_, v_a_810_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___boxed(lean_object* v_e_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_Meta_Sym_isBoolFalseExpr(v_e_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec_ref(v_e_818_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg(lean_object* v_a_827_){
_start:
{
lean_object* v___x_829_; lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_838_; 
v___x_829_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_827_);
v_a_830_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_838_ == 0)
{
v___x_832_ = v___x_829_;
v_isShared_833_ = v_isSharedCheck_838_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_829_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_838_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v_natZExpr_834_; lean_object* v___x_836_; 
v_natZExpr_834_ = lean_ctor_get(v_a_830_, 2);
lean_inc_ref(v_natZExpr_834_);
lean_dec(v_a_830_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 0, v_natZExpr_834_);
v___x_836_ = v___x_832_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_natZExpr_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___redArg___boxed(lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_839_);
lean_dec_ref(v_a_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr(lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_842_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatZeroExpr___boxed(lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_Meta_Sym_getNatZeroExpr(v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg(lean_object* v_a_858_){
_start:
{
lean_object* v___x_860_; lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_869_; 
v___x_860_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_858_);
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_869_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v_ordEqExpr_865_; lean_object* v___x_867_; 
v_ordEqExpr_865_ = lean_ctor_get(v_a_861_, 5);
lean_inc_ref(v_ordEqExpr_865_);
lean_dec(v_a_861_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v_ordEqExpr_865_);
v___x_867_ = v___x_863_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_ordEqExpr_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg___boxed(lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_870_);
lean_dec_ref(v_a_870_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr(lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_873_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___boxed(lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_Meta_Sym_getOrderingEqExpr(v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg(lean_object* v_a_889_){
_start:
{
lean_object* v___x_891_; lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_900_; 
v___x_891_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_889_);
v_a_892_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_900_ == 0)
{
v___x_894_ = v___x_891_;
v_isShared_895_ = v_isSharedCheck_900_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_900_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v_intExpr_896_; lean_object* v___x_898_; 
v_intExpr_896_ = lean_ctor_get(v_a_892_, 6);
lean_inc_ref(v_intExpr_896_);
lean_dec(v_a_892_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v_intExpr_896_);
v___x_898_ = v___x_894_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_intExpr_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___redArg___boxed(lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_901_);
lean_dec_ref(v_a_901_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr(lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_904_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntExpr___boxed(lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_Meta_Sym_getIntExpr(v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_920_, lean_object* v_vals_921_, lean_object* v_i_922_, lean_object* v_k_923_){
_start:
{
lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_924_ = lean_array_get_size(v_keys_920_);
v___x_925_ = lean_nat_dec_lt(v_i_922_, v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; 
lean_dec_ref(v_k_923_);
lean_dec(v_i_922_);
v___x_926_ = lean_box(0);
return v___x_926_;
}
else
{
lean_object* v_k_x27_927_; uint8_t v___x_928_; 
v_k_x27_927_ = lean_array_fget_borrowed(v_keys_920_, v_i_922_);
lean_inc(v_k_x27_927_);
lean_inc_ref(v_k_923_);
v___x_928_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_923_, v_k_x27_927_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = lean_unsigned_to_nat(1u);
v___x_930_ = lean_nat_add(v_i_922_, v___x_929_);
lean_dec(v_i_922_);
v_i_922_ = v___x_930_;
goto _start;
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
lean_dec_ref(v_k_923_);
v___x_932_ = lean_array_fget_borrowed(v_vals_921_, v_i_922_);
lean_dec(v_i_922_);
lean_inc(v___x_932_);
lean_inc(v_k_x27_927_);
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v_k_x27_927_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
return v___x_934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_935_, lean_object* v_vals_936_, lean_object* v_i_937_, lean_object* v_k_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg(v_keys_935_, v_vals_936_, v_i_937_, v_k_938_);
lean_dec_ref(v_vals_936_);
lean_dec_ref(v_keys_935_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg(lean_object* v_x_940_, size_t v_x_941_, lean_object* v_x_942_){
_start:
{
if (lean_obj_tag(v_x_940_) == 0)
{
lean_object* v_es_943_; lean_object* v___x_944_; size_t v___x_945_; size_t v___x_946_; lean_object* v_j_947_; lean_object* v___x_948_; 
v_es_943_ = lean_ctor_get(v_x_940_, 0);
lean_inc_ref(v_es_943_);
lean_dec_ref_known(v_x_940_, 1);
v___x_944_ = lean_box(2);
v___x_945_ = ((size_t)31ULL);
v___x_946_ = lean_usize_land(v_x_941_, v___x_945_);
v_j_947_ = lean_usize_to_nat(v___x_946_);
v___x_948_ = lean_array_get(v___x_944_, v_es_943_, v_j_947_);
lean_dec(v_j_947_);
lean_dec_ref(v_es_943_);
switch(lean_obj_tag(v___x_948_))
{
case 0:
{
lean_object* v_key_949_; lean_object* v_val_950_; uint8_t v___x_951_; 
v_key_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc_n(v_key_949_, 2);
v_val_950_ = lean_ctor_get(v___x_948_, 1);
lean_inc(v_val_950_);
lean_dec_ref_known(v___x_948_, 2);
v___x_951_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_942_, v_key_949_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; 
lean_dec(v_val_950_);
lean_dec(v_key_949_);
v___x_952_ = lean_box(0);
return v___x_952_;
}
else
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_953_, 0, v_key_949_);
lean_ctor_set(v___x_953_, 1, v_val_950_);
v___x_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
return v___x_954_;
}
}
case 1:
{
lean_object* v_node_955_; size_t v___x_956_; size_t v___x_957_; 
v_node_955_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_node_955_);
lean_dec_ref_known(v___x_948_, 1);
v___x_956_ = ((size_t)5ULL);
v___x_957_ = lean_usize_shift_right(v_x_941_, v___x_956_);
v_x_940_ = v_node_955_;
v_x_941_ = v___x_957_;
goto _start;
}
default: 
{
lean_object* v___x_959_; 
lean_dec_ref(v_x_942_);
v___x_959_ = lean_box(0);
return v___x_959_;
}
}
}
else
{
lean_object* v_ks_960_; lean_object* v_vs_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v_ks_960_ = lean_ctor_get(v_x_940_, 0);
lean_inc_ref(v_ks_960_);
v_vs_961_ = lean_ctor_get(v_x_940_, 1);
lean_inc_ref(v_vs_961_);
lean_dec_ref_known(v_x_940_, 2);
v___x_962_ = lean_unsigned_to_nat(0u);
v___x_963_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg(v_ks_960_, v_vs_961_, v___x_962_, v_x_942_);
lean_dec_ref(v_vs_961_);
lean_dec_ref(v_ks_960_);
return v___x_963_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___boxed(lean_object* v_x_964_, lean_object* v_x_965_, lean_object* v_x_966_){
_start:
{
size_t v_x_2077__boxed_967_; lean_object* v_res_968_; 
v_x_2077__boxed_967_ = lean_unbox_usize(v_x_965_);
lean_dec(v_x_965_);
v_res_968_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg(v_x_964_, v_x_2077__boxed_967_, v_x_966_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg(lean_object* v_x_969_, lean_object* v_x_970_){
_start:
{
uint64_t v___x_971_; size_t v___x_972_; lean_object* v___x_973_; 
v___x_971_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_970_);
v___x_972_ = lean_uint64_to_usize(v___x_971_);
lean_inc_ref(v_x_969_);
v___x_973_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg(v_x_969_, v___x_972_, v_x_970_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg___boxed(lean_object* v_x_974_, lean_object* v_x_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg(v_x_974_, v_x_975_);
lean_dec_ref(v_x_974_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object* v_e_977_, lean_object* v_a_978_){
_start:
{
lean_object* v___x_980_; lean_object* v_share_981_; lean_object* v_maxFVar_982_; lean_object* v_proofInstInfo_983_; lean_object* v_inferType_984_; lean_object* v_getLevel_985_; lean_object* v_congrInfo_986_; lean_object* v_defEqI_987_; lean_object* v_extensions_988_; lean_object* v_issues_989_; lean_object* v_canon_990_; uint8_t v_debug_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1033_; 
v___x_980_ = lean_st_ref_take(v_a_978_);
v_share_981_ = lean_ctor_get(v___x_980_, 0);
v_maxFVar_982_ = lean_ctor_get(v___x_980_, 1);
v_proofInstInfo_983_ = lean_ctor_get(v___x_980_, 2);
v_inferType_984_ = lean_ctor_get(v___x_980_, 3);
v_getLevel_985_ = lean_ctor_get(v___x_980_, 4);
v_congrInfo_986_ = lean_ctor_get(v___x_980_, 5);
v_defEqI_987_ = lean_ctor_get(v___x_980_, 6);
v_extensions_988_ = lean_ctor_get(v___x_980_, 7);
v_issues_989_ = lean_ctor_get(v___x_980_, 8);
v_canon_990_ = lean_ctor_get(v___x_980_, 9);
v_debug_991_ = lean_ctor_get_uint8(v___x_980_, sizeof(void*)*10);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_993_ = v___x_980_;
v_isShared_994_ = v_isSharedCheck_1033_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_canon_990_);
lean_inc(v_issues_989_);
lean_inc(v_extensions_988_);
lean_inc(v_defEqI_987_);
lean_inc(v_congrInfo_986_);
lean_inc(v_getLevel_985_);
lean_inc(v_inferType_984_);
lean_inc(v_proofInstInfo_983_);
lean_inc(v_maxFVar_982_);
lean_inc(v_share_981_);
lean_dec(v___x_980_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1033_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_995_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__0, &l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v___x_995_);
v___x_997_ = v___x_993_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_maxFVar_982_);
lean_ctor_set(v_reuseFailAlloc_1032_, 2, v_proofInstInfo_983_);
lean_ctor_set(v_reuseFailAlloc_1032_, 3, v_inferType_984_);
lean_ctor_set(v_reuseFailAlloc_1032_, 4, v_getLevel_985_);
lean_ctor_set(v_reuseFailAlloc_1032_, 5, v_congrInfo_986_);
lean_ctor_set(v_reuseFailAlloc_1032_, 6, v_defEqI_987_);
lean_ctor_set(v_reuseFailAlloc_1032_, 7, v_extensions_988_);
lean_ctor_set(v_reuseFailAlloc_1032_, 8, v_issues_989_);
lean_ctor_set(v_reuseFailAlloc_1032_, 9, v_canon_990_);
lean_ctor_set_uint8(v_reuseFailAlloc_1032_, sizeof(void*)*10, v_debug_991_);
v___x_997_ = v_reuseFailAlloc_1032_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_998_; lean_object* v_fst_1000_; lean_object* v_snd_1001_; lean_object* v___x_1023_; 
v___x_998_ = lean_st_ref_set(v_a_978_, v___x_997_);
lean_inc_ref(v_e_977_);
v___x_1023_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg(v_share_981_, v_e_977_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v_snd_1027_; lean_object* v_fst_1028_; lean_object* v_set_1029_; 
v___x_1024_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__4, &l_Lean_Meta_Sym_SymM_run___redArg___closed__4_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__4);
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v_share_981_);
v___x_1026_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_977_, v___x_1025_);
v_snd_1027_ = lean_ctor_get(v___x_1026_, 1);
lean_inc(v_snd_1027_);
v_fst_1028_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_fst_1028_);
lean_dec_ref(v___x_1026_);
v_set_1029_ = lean_ctor_get(v_snd_1027_, 1);
lean_inc_ref(v_set_1029_);
lean_dec(v_snd_1027_);
v_fst_1000_ = v_fst_1028_;
v_snd_1001_ = v_set_1029_;
goto v___jp_999_;
}
else
{
lean_object* v_val_1030_; lean_object* v_fst_1031_; 
lean_dec_ref(v_e_977_);
v_val_1030_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_val_1030_);
lean_dec_ref_known(v___x_1023_, 1);
v_fst_1031_ = lean_ctor_get(v_val_1030_, 0);
lean_inc(v_fst_1031_);
lean_dec(v_val_1030_);
v_fst_1000_ = v_fst_1031_;
v_snd_1001_ = v_share_981_;
goto v___jp_999_;
}
v___jp_999_:
{
lean_object* v___x_1002_; lean_object* v_maxFVar_1003_; lean_object* v_proofInstInfo_1004_; lean_object* v_inferType_1005_; lean_object* v_getLevel_1006_; lean_object* v_congrInfo_1007_; lean_object* v_defEqI_1008_; lean_object* v_extensions_1009_; lean_object* v_issues_1010_; lean_object* v_canon_1011_; uint8_t v_debug_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1021_; 
v___x_1002_ = lean_st_ref_take(v_a_978_);
v_maxFVar_1003_ = lean_ctor_get(v___x_1002_, 1);
v_proofInstInfo_1004_ = lean_ctor_get(v___x_1002_, 2);
v_inferType_1005_ = lean_ctor_get(v___x_1002_, 3);
v_getLevel_1006_ = lean_ctor_get(v___x_1002_, 4);
v_congrInfo_1007_ = lean_ctor_get(v___x_1002_, 5);
v_defEqI_1008_ = lean_ctor_get(v___x_1002_, 6);
v_extensions_1009_ = lean_ctor_get(v___x_1002_, 7);
v_issues_1010_ = lean_ctor_get(v___x_1002_, 8);
v_canon_1011_ = lean_ctor_get(v___x_1002_, 9);
v_debug_1012_ = lean_ctor_get_uint8(v___x_1002_, sizeof(void*)*10);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; 
v_unused_1022_ = lean_ctor_get(v___x_1002_, 0);
lean_dec(v_unused_1022_);
v___x_1014_ = v___x_1002_;
v_isShared_1015_ = v_isSharedCheck_1021_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_canon_1011_);
lean_inc(v_issues_1010_);
lean_inc(v_extensions_1009_);
lean_inc(v_defEqI_1008_);
lean_inc(v_congrInfo_1007_);
lean_inc(v_getLevel_1006_);
lean_inc(v_inferType_1005_);
lean_inc(v_proofInstInfo_1004_);
lean_inc(v_maxFVar_1003_);
lean_dec(v___x_1002_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1021_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v_snd_1001_);
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_snd_1001_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_maxFVar_1003_);
lean_ctor_set(v_reuseFailAlloc_1020_, 2, v_proofInstInfo_1004_);
lean_ctor_set(v_reuseFailAlloc_1020_, 3, v_inferType_1005_);
lean_ctor_set(v_reuseFailAlloc_1020_, 4, v_getLevel_1006_);
lean_ctor_set(v_reuseFailAlloc_1020_, 5, v_congrInfo_1007_);
lean_ctor_set(v_reuseFailAlloc_1020_, 6, v_defEqI_1008_);
lean_ctor_set(v_reuseFailAlloc_1020_, 7, v_extensions_1009_);
lean_ctor_set(v_reuseFailAlloc_1020_, 8, v_issues_1010_);
lean_ctor_set(v_reuseFailAlloc_1020_, 9, v_canon_1011_);
lean_ctor_set_uint8(v_reuseFailAlloc_1020_, sizeof(void*)*10, v_debug_1012_);
v___x_1017_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_st_ref_set(v_a_978_, v___x_1017_);
v___x_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1019_, 0, v_fst_1000_);
return v___x_1019_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___redArg___boxed(lean_object* v_e_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_Meta_Sym_shareCommon___redArg(v_e_1034_, v_a_1035_);
lean_dec(v_a_1035_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon(lean_object* v_e_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_Meta_Sym_shareCommon___redArg(v_e_1038_, v_a_1040_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___boxed(lean_object* v_e_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_Meta_Sym_shareCommon(v_e_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0(lean_object* v_00_u03b2_1056_, lean_object* v_x_1057_, lean_object* v_x_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg(v_x_1057_, v_x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___boxed(lean_object* v_00_u03b2_1060_, lean_object* v_x_1061_, lean_object* v_x_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0(v_00_u03b2_1060_, v_x_1061_, v_x_1062_);
lean_dec_ref(v_x_1061_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0(lean_object* v_00_u03b2_1064_, lean_object* v_x_1065_, size_t v_x_1066_, lean_object* v_x_1067_){
_start:
{
lean_object* v___x_1068_; 
lean_inc_ref(v_x_1065_);
v___x_1068_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg(v_x_1065_, v_x_1066_, v_x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_, lean_object* v_x_1072_){
_start:
{
size_t v_x_2233__boxed_1073_; lean_object* v_res_1074_; 
v_x_2233__boxed_1073_ = lean_unbox_usize(v_x_1071_);
lean_dec(v_x_1071_);
v_res_1074_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0(v_00_u03b2_1069_, v_x_1070_, v_x_2233__boxed_1073_, v_x_1072_);
lean_dec_ref(v_x_1070_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1075_, lean_object* v_keys_1076_, lean_object* v_vals_1077_, lean_object* v_heq_1078_, lean_object* v_i_1079_, lean_object* v_k_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg(v_keys_1076_, v_vals_1077_, v_i_1079_, v_k_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1082_, lean_object* v_keys_1083_, lean_object* v_vals_1084_, lean_object* v_heq_1085_, lean_object* v_i_1086_, lean_object* v_k_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1(v_00_u03b2_1082_, v_keys_1083_, v_vals_1084_, v_heq_1085_, v_i_1086_, v_k_1087_);
lean_dec_ref(v_vals_1084_);
lean_dec_ref(v_keys_1083_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object* v_e_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v___x_1092_; lean_object* v_share_1093_; lean_object* v_maxFVar_1094_; lean_object* v_proofInstInfo_1095_; lean_object* v_inferType_1096_; lean_object* v_getLevel_1097_; lean_object* v_congrInfo_1098_; lean_object* v_defEqI_1099_; lean_object* v_extensions_1100_; lean_object* v_issues_1101_; lean_object* v_canon_1102_; uint8_t v_debug_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1136_; 
v___x_1092_ = lean_st_ref_take(v_a_1090_);
v_share_1093_ = lean_ctor_get(v___x_1092_, 0);
v_maxFVar_1094_ = lean_ctor_get(v___x_1092_, 1);
v_proofInstInfo_1095_ = lean_ctor_get(v___x_1092_, 2);
v_inferType_1096_ = lean_ctor_get(v___x_1092_, 3);
v_getLevel_1097_ = lean_ctor_get(v___x_1092_, 4);
v_congrInfo_1098_ = lean_ctor_get(v___x_1092_, 5);
v_defEqI_1099_ = lean_ctor_get(v___x_1092_, 6);
v_extensions_1100_ = lean_ctor_get(v___x_1092_, 7);
v_issues_1101_ = lean_ctor_get(v___x_1092_, 8);
v_canon_1102_ = lean_ctor_get(v___x_1092_, 9);
v_debug_1103_ = lean_ctor_get_uint8(v___x_1092_, sizeof(void*)*10);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1105_ = v___x_1092_;
v_isShared_1106_ = v_isSharedCheck_1136_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_canon_1102_);
lean_inc(v_issues_1101_);
lean_inc(v_extensions_1100_);
lean_inc(v_defEqI_1099_);
lean_inc(v_congrInfo_1098_);
lean_inc(v_getLevel_1097_);
lean_inc(v_inferType_1096_);
lean_inc(v_proofInstInfo_1095_);
lean_inc(v_maxFVar_1094_);
lean_inc(v_share_1093_);
lean_dec(v___x_1092_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1136_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1107_; lean_object* v___x_1109_; 
v___x_1107_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__0, &l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v___x_1107_);
v___x_1109_ = v___x_1105_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_maxFVar_1094_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_proofInstInfo_1095_);
lean_ctor_set(v_reuseFailAlloc_1135_, 3, v_inferType_1096_);
lean_ctor_set(v_reuseFailAlloc_1135_, 4, v_getLevel_1097_);
lean_ctor_set(v_reuseFailAlloc_1135_, 5, v_congrInfo_1098_);
lean_ctor_set(v_reuseFailAlloc_1135_, 6, v_defEqI_1099_);
lean_ctor_set(v_reuseFailAlloc_1135_, 7, v_extensions_1100_);
lean_ctor_set(v_reuseFailAlloc_1135_, 8, v_issues_1101_);
lean_ctor_set(v_reuseFailAlloc_1135_, 9, v_canon_1102_);
lean_ctor_set_uint8(v_reuseFailAlloc_1135_, sizeof(void*)*10, v_debug_1103_);
v___x_1109_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v_fst_1112_; lean_object* v_snd_1113_; lean_object* v___x_1114_; lean_object* v_maxFVar_1115_; lean_object* v_proofInstInfo_1116_; lean_object* v_inferType_1117_; lean_object* v_getLevel_1118_; lean_object* v_congrInfo_1119_; lean_object* v_defEqI_1120_; lean_object* v_extensions_1121_; lean_object* v_issues_1122_; lean_object* v_canon_1123_; uint8_t v_debug_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1133_; 
v___x_1110_ = lean_st_ref_set(v_a_1090_, v___x_1109_);
v___x_1111_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1089_, v_share_1093_);
v_fst_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_fst_1112_);
v_snd_1113_ = lean_ctor_get(v___x_1111_, 1);
lean_inc(v_snd_1113_);
lean_dec_ref(v___x_1111_);
v___x_1114_ = lean_st_ref_take(v_a_1090_);
v_maxFVar_1115_ = lean_ctor_get(v___x_1114_, 1);
v_proofInstInfo_1116_ = lean_ctor_get(v___x_1114_, 2);
v_inferType_1117_ = lean_ctor_get(v___x_1114_, 3);
v_getLevel_1118_ = lean_ctor_get(v___x_1114_, 4);
v_congrInfo_1119_ = lean_ctor_get(v___x_1114_, 5);
v_defEqI_1120_ = lean_ctor_get(v___x_1114_, 6);
v_extensions_1121_ = lean_ctor_get(v___x_1114_, 7);
v_issues_1122_ = lean_ctor_get(v___x_1114_, 8);
v_canon_1123_ = lean_ctor_get(v___x_1114_, 9);
v_debug_1124_ = lean_ctor_get_uint8(v___x_1114_, sizeof(void*)*10);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1133_ == 0)
{
lean_object* v_unused_1134_; 
v_unused_1134_ = lean_ctor_get(v___x_1114_, 0);
lean_dec(v_unused_1134_);
v___x_1126_ = v___x_1114_;
v_isShared_1127_ = v_isSharedCheck_1133_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_canon_1123_);
lean_inc(v_issues_1122_);
lean_inc(v_extensions_1121_);
lean_inc(v_defEqI_1120_);
lean_inc(v_congrInfo_1119_);
lean_inc(v_getLevel_1118_);
lean_inc(v_inferType_1117_);
lean_inc(v_proofInstInfo_1116_);
lean_inc(v_maxFVar_1115_);
lean_dec(v___x_1114_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1133_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v_snd_1113_);
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_snd_1113_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_maxFVar_1115_);
lean_ctor_set(v_reuseFailAlloc_1132_, 2, v_proofInstInfo_1116_);
lean_ctor_set(v_reuseFailAlloc_1132_, 3, v_inferType_1117_);
lean_ctor_set(v_reuseFailAlloc_1132_, 4, v_getLevel_1118_);
lean_ctor_set(v_reuseFailAlloc_1132_, 5, v_congrInfo_1119_);
lean_ctor_set(v_reuseFailAlloc_1132_, 6, v_defEqI_1120_);
lean_ctor_set(v_reuseFailAlloc_1132_, 7, v_extensions_1121_);
lean_ctor_set(v_reuseFailAlloc_1132_, 8, v_issues_1122_);
lean_ctor_set(v_reuseFailAlloc_1132_, 9, v_canon_1123_);
lean_ctor_set_uint8(v_reuseFailAlloc_1132_, sizeof(void*)*10, v_debug_1124_);
v___x_1129_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_st_ref_set(v_a_1090_, v___x_1129_);
v___x_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1131_, 0, v_fst_1112_);
return v___x_1131_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg___boxed(lean_object* v_e_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_e_1137_, v_a_1138_);
lean_dec(v_a_1138_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object* v_e_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_e_1141_, v_a_1143_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___boxed(lean_object* v_e_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lean_Meta_Sym_shareCommonInc(v_e_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___redArg(lean_object* v_e_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_e_1159_, v_a_1160_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___redArg___boxed(lean_object* v_e_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_Meta_Sym_share___redArg(v_e_1163_, v_a_1164_);
lean_dec(v_a_1164_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share(lean_object* v_e_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_e_1167_, v_a_1169_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___boxed(lean_object* v_e_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_Meta_Sym_share(v_e_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
lean_dec(v_a_1180_);
lean_dec_ref(v_a_1179_);
lean_dec(v_a_1178_);
lean_dec_ref(v_a_1177_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg(lean_object* v_a_1185_){
_start:
{
lean_object* v___x_1187_; uint8_t v_debug_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1187_ = lean_st_ref_get(v_a_1185_);
v_debug_1188_ = lean_ctor_get_uint8(v___x_1187_, sizeof(void*)*10);
lean_dec(v___x_1187_);
v___x_1189_ = lean_box(v_debug_1188_);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg___boxed(lean_object* v_a_1191_, lean_object* v_a_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_Meta_Sym_isDebugEnabled___redArg(v_a_1191_);
lean_dec(v_a_1191_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled(lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_){
_start:
{
lean_object* v___x_1201_; uint8_t v_debug_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1201_ = lean_st_ref_get(v_a_1195_);
v_debug_1202_ = lean_ctor_get_uint8(v___x_1201_, sizeof(void*)*10);
lean_dec(v___x_1201_);
v___x_1203_ = lean_box(v_debug_1202_);
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___boxed(lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_Meta_Sym_isDebugEnabled(v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
lean_dec(v_a_1210_);
lean_dec_ref(v_a_1209_);
lean_dec(v_a_1208_);
lean_dec_ref(v_a_1207_);
lean_dec(v_a_1206_);
lean_dec_ref(v_a_1205_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object* v_a_1213_){
_start:
{
uint8_t v_config_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v_config_1215_ = lean_ctor_get_uint8(v_a_1213_, sizeof(void*)*1);
v___x_1216_ = lean_box(v_config_1215_);
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg___boxed(lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1218_);
lean_dec_ref(v_a_1218_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig(lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1221_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___boxed(lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_Meta_Sym_getConfig(v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Sym_reportIssue_spec__0(lean_object* v_msgData_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v___x_1243_; lean_object* v_env_1244_; lean_object* v___x_1245_; lean_object* v_mctx_1246_; lean_object* v_lctx_1247_; lean_object* v_options_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1243_ = lean_st_ref_get(v___y_1241_);
v_env_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc_ref(v_env_1244_);
lean_dec(v___x_1243_);
v___x_1245_ = lean_st_ref_get(v___y_1239_);
v_mctx_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc_ref(v_mctx_1246_);
lean_dec(v___x_1245_);
v_lctx_1247_ = lean_ctor_get(v___y_1238_, 2);
v_options_1248_ = lean_ctor_get(v___y_1240_, 2);
lean_inc_ref(v_options_1248_);
lean_inc_ref(v_lctx_1247_);
v___x_1249_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1249_, 0, v_env_1244_);
lean_ctor_set(v___x_1249_, 1, v_mctx_1246_);
lean_ctor_set(v___x_1249_, 2, v_lctx_1247_);
lean_ctor_set(v___x_1249_, 3, v_options_1248_);
v___x_1250_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
lean_ctor_set(v___x_1250_, 1, v_msgData_1237_);
v___x_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Sym_reportIssue_spec__0___boxed(lean_object* v_msgData_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Sym_reportIssue_spec__0(v_msgData_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
return v_res_1258_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1259_; double v___x_1260_; 
v___x_1259_ = lean_unsigned_to_nat(0u);
v___x_1260_ = lean_float_of_nat(v___x_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg(lean_object* v_cls_1264_, lean_object* v_msg_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v_ref_1271_; lean_object* v___x_1272_; lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1317_; 
v_ref_1271_ = lean_ctor_get(v___y_1268_, 5);
v___x_1272_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Sym_reportIssue_spec__0(v_msg_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1275_ = v___x_1272_;
v_isShared_1276_ = v_isSharedCheck_1317_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1317_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; lean_object* v_traceState_1278_; lean_object* v_env_1279_; lean_object* v_nextMacroScope_1280_; lean_object* v_ngen_1281_; lean_object* v_auxDeclNGen_1282_; lean_object* v_cache_1283_; lean_object* v_messages_1284_; lean_object* v_infoState_1285_; lean_object* v_snapshotTasks_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1316_; 
v___x_1277_ = lean_st_ref_take(v___y_1269_);
v_traceState_1278_ = lean_ctor_get(v___x_1277_, 4);
v_env_1279_ = lean_ctor_get(v___x_1277_, 0);
v_nextMacroScope_1280_ = lean_ctor_get(v___x_1277_, 1);
v_ngen_1281_ = lean_ctor_get(v___x_1277_, 2);
v_auxDeclNGen_1282_ = lean_ctor_get(v___x_1277_, 3);
v_cache_1283_ = lean_ctor_get(v___x_1277_, 5);
v_messages_1284_ = lean_ctor_get(v___x_1277_, 6);
v_infoState_1285_ = lean_ctor_get(v___x_1277_, 7);
v_snapshotTasks_1286_ = lean_ctor_get(v___x_1277_, 8);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1288_ = v___x_1277_;
v_isShared_1289_ = v_isSharedCheck_1316_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_snapshotTasks_1286_);
lean_inc(v_infoState_1285_);
lean_inc(v_messages_1284_);
lean_inc(v_cache_1283_);
lean_inc(v_traceState_1278_);
lean_inc(v_auxDeclNGen_1282_);
lean_inc(v_ngen_1281_);
lean_inc(v_nextMacroScope_1280_);
lean_inc(v_env_1279_);
lean_dec(v___x_1277_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1316_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
uint64_t v_tid_1290_; lean_object* v_traces_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1315_; 
v_tid_1290_ = lean_ctor_get_uint64(v_traceState_1278_, sizeof(void*)*1);
v_traces_1291_ = lean_ctor_get(v_traceState_1278_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v_traceState_1278_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1293_ = v_traceState_1278_;
v_isShared_1294_ = v_isSharedCheck_1315_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_traces_1291_);
lean_dec(v_traceState_1278_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1315_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1295_; double v___x_1296_; uint8_t v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1295_ = lean_box(0);
v___x_1296_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0);
v___x_1297_ = 0;
v___x_1298_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__1));
v___x_1299_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1299_, 0, v_cls_1264_);
lean_ctor_set(v___x_1299_, 1, v___x_1295_);
lean_ctor_set(v___x_1299_, 2, v___x_1298_);
lean_ctor_set_float(v___x_1299_, sizeof(void*)*3, v___x_1296_);
lean_ctor_set_float(v___x_1299_, sizeof(void*)*3 + 8, v___x_1296_);
lean_ctor_set_uint8(v___x_1299_, sizeof(void*)*3 + 16, v___x_1297_);
v___x_1300_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__2));
v___x_1301_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1299_);
lean_ctor_set(v___x_1301_, 1, v_a_1273_);
lean_ctor_set(v___x_1301_, 2, v___x_1300_);
lean_inc(v_ref_1271_);
v___x_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1302_, 0, v_ref_1271_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
v___x_1303_ = l_Lean_PersistentArray_push___redArg(v_traces_1291_, v___x_1302_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v___x_1303_);
v___x_1305_ = v___x_1293_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1303_);
lean_ctor_set_uint64(v_reuseFailAlloc_1314_, sizeof(void*)*1, v_tid_1290_);
v___x_1305_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1307_; 
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 4, v___x_1305_);
v___x_1307_ = v___x_1288_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_env_1279_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_nextMacroScope_1280_);
lean_ctor_set(v_reuseFailAlloc_1313_, 2, v_ngen_1281_);
lean_ctor_set(v_reuseFailAlloc_1313_, 3, v_auxDeclNGen_1282_);
lean_ctor_set(v_reuseFailAlloc_1313_, 4, v___x_1305_);
lean_ctor_set(v_reuseFailAlloc_1313_, 5, v_cache_1283_);
lean_ctor_set(v_reuseFailAlloc_1313_, 6, v_messages_1284_);
lean_ctor_set(v_reuseFailAlloc_1313_, 7, v_infoState_1285_);
lean_ctor_set(v_reuseFailAlloc_1313_, 8, v_snapshotTasks_1286_);
v___x_1307_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1311_; 
v___x_1308_ = lean_st_ref_set(v___y_1269_, v___x_1307_);
v___x_1309_ = lean_box(0);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1309_);
v___x_1311_ = v___x_1275_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___boxed(lean_object* v_cls_1318_, lean_object* v_msg_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg(v_cls_1318_, v_msg_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
return v_res_1325_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_reportIssue___closed__2(void){
_start:
{
lean_object* v___x_1329_; uint8_t v___x_1330_; double v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1329_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__1));
v___x_1330_ = 1;
v___x_1331_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0);
v___x_1332_ = lean_box(0);
v___x_1333_ = ((lean_object*)(l_Lean_Meta_Sym_reportIssue___closed__1));
v___x_1334_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set(v___x_1334_, 1, v___x_1332_);
lean_ctor_set(v___x_1334_, 2, v___x_1329_);
lean_ctor_set_float(v___x_1334_, sizeof(void*)*3, v___x_1331_);
lean_ctor_set_float(v___x_1334_, sizeof(void*)*3 + 8, v___x_1331_);
lean_ctor_set_uint8(v___x_1334_, sizeof(void*)*3 + 16, v___x_1330_);
return v___x_1334_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_reportIssue___closed__5(void){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1338_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_1339_ = ((lean_object*)(l_Lean_Meta_Sym_reportIssue___closed__4));
v___x_1340_ = l_Lean_Name_append(v___x_1339_, v___x_1338_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue(lean_object* v_msg_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v___x_1352_; lean_object* v_a_1353_; lean_object* v___x_1354_; lean_object* v_share_1355_; lean_object* v_maxFVar_1356_; lean_object* v_proofInstInfo_1357_; lean_object* v_inferType_1358_; lean_object* v_getLevel_1359_; lean_object* v_congrInfo_1360_; lean_object* v_defEqI_1361_; lean_object* v_extensions_1362_; lean_object* v_issues_1363_; lean_object* v_canon_1364_; uint8_t v_debug_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1384_; 
v___x_1352_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Sym_reportIssue_spec__0(v_msg_1341_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_a_1353_);
lean_dec_ref(v___x_1352_);
v___x_1354_ = lean_st_ref_take(v_a_1343_);
v_share_1355_ = lean_ctor_get(v___x_1354_, 0);
v_maxFVar_1356_ = lean_ctor_get(v___x_1354_, 1);
v_proofInstInfo_1357_ = lean_ctor_get(v___x_1354_, 2);
v_inferType_1358_ = lean_ctor_get(v___x_1354_, 3);
v_getLevel_1359_ = lean_ctor_get(v___x_1354_, 4);
v_congrInfo_1360_ = lean_ctor_get(v___x_1354_, 5);
v_defEqI_1361_ = lean_ctor_get(v___x_1354_, 6);
v_extensions_1362_ = lean_ctor_get(v___x_1354_, 7);
v_issues_1363_ = lean_ctor_get(v___x_1354_, 8);
v_canon_1364_ = lean_ctor_get(v___x_1354_, 9);
v_debug_1365_ = lean_ctor_get_uint8(v___x_1354_, sizeof(void*)*10);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1367_ = v___x_1354_;
v_isShared_1368_ = v_isSharedCheck_1384_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_canon_1364_);
lean_inc(v_issues_1363_);
lean_inc(v_extensions_1362_);
lean_inc(v_defEqI_1361_);
lean_inc(v_congrInfo_1360_);
lean_inc(v_getLevel_1359_);
lean_inc(v_inferType_1358_);
lean_inc(v_proofInstInfo_1357_);
lean_inc(v_maxFVar_1356_);
lean_inc(v_share_1355_);
lean_dec(v___x_1354_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1384_;
goto v_resetjp_1366_;
}
v___jp_1349_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1350_ = lean_box(0);
v___x_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
return v___x_1351_;
}
v_resetjp_1366_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1374_; 
v___x_1369_ = lean_obj_once(&l_Lean_Meta_Sym_reportIssue___closed__2, &l_Lean_Meta_Sym_reportIssue___closed__2_once, _init_l_Lean_Meta_Sym_reportIssue___closed__2);
v___x_1370_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__2));
lean_inc(v_a_1353_);
v___x_1371_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1369_);
lean_ctor_set(v___x_1371_, 1, v_a_1353_);
lean_ctor_set(v___x_1371_, 2, v___x_1370_);
v___x_1372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
lean_ctor_set(v___x_1372_, 1, v_issues_1363_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 8, v___x_1372_);
v___x_1374_ = v___x_1367_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_share_1355_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_maxFVar_1356_);
lean_ctor_set(v_reuseFailAlloc_1383_, 2, v_proofInstInfo_1357_);
lean_ctor_set(v_reuseFailAlloc_1383_, 3, v_inferType_1358_);
lean_ctor_set(v_reuseFailAlloc_1383_, 4, v_getLevel_1359_);
lean_ctor_set(v_reuseFailAlloc_1383_, 5, v_congrInfo_1360_);
lean_ctor_set(v_reuseFailAlloc_1383_, 6, v_defEqI_1361_);
lean_ctor_set(v_reuseFailAlloc_1383_, 7, v_extensions_1362_);
lean_ctor_set(v_reuseFailAlloc_1383_, 8, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1383_, 9, v_canon_1364_);
lean_ctor_set_uint8(v_reuseFailAlloc_1383_, sizeof(void*)*10, v_debug_1365_);
v___x_1374_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1375_; lean_object* v_options_1376_; uint8_t v_hasTrace_1377_; 
v___x_1375_ = lean_st_ref_set(v_a_1343_, v___x_1374_);
v_options_1376_ = lean_ctor_get(v_a_1346_, 2);
v_hasTrace_1377_ = lean_ctor_get_uint8(v_options_1376_, sizeof(void*)*1);
if (v_hasTrace_1377_ == 0)
{
lean_dec(v_a_1353_);
goto v___jp_1349_;
}
else
{
lean_object* v_inheritedTraceOptions_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; uint8_t v___x_1381_; 
v_inheritedTraceOptions_1378_ = lean_ctor_get(v_a_1346_, 13);
v___x_1379_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_1380_ = lean_obj_once(&l_Lean_Meta_Sym_reportIssue___closed__5, &l_Lean_Meta_Sym_reportIssue___closed__5_once, _init_l_Lean_Meta_Sym_reportIssue___closed__5);
v___x_1381_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1378_, v_options_1376_, v___x_1380_);
if (v___x_1381_ == 0)
{
lean_dec(v_a_1353_);
goto v___jp_1349_;
}
else
{
lean_object* v___x_1382_; 
v___x_1382_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg(v___x_1379_, v_a_1353_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
return v___x_1382_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue___boxed(lean_object* v_msg_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_Meta_Sym_reportIssue(v_msg_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
lean_dec(v_a_1389_);
lean_dec_ref(v_a_1388_);
lean_dec(v_a_1387_);
lean_dec_ref(v_a_1386_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1(lean_object* v_cls_1394_, lean_object* v_msg_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg(v_cls_1394_, v_msg_1395_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___boxed(lean_object* v_cls_1404_, lean_object* v_msg_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1(v_cls_1404_, v_msg_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose(lean_object* v_msg_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_){
_start:
{
lean_object* v___x_1422_; lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1433_; 
v___x_1422_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1415_);
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1425_ = v___x_1422_;
v_isShared_1426_ = v_isSharedCheck_1433_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1422_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1433_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
uint8_t v___x_1427_; 
v___x_1427_ = lean_unbox(v_a_1423_);
lean_dec(v_a_1423_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; lean_object* v___x_1430_; 
lean_dec_ref(v_msg_1414_);
v___x_1428_ = lean_box(0);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1428_);
v___x_1430_ = v___x_1425_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
else
{
lean_object* v___x_1432_; 
lean_del_object(v___x_1425_);
v___x_1432_ = l_Lean_Meta_Sym_reportIssue(v_msg_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_);
return v___x_1432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose___boxed(lean_object* v_msg_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_Meta_Sym_reportIssueIfVerbose(v_msg_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
return v_res_1442_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7(void){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6));
v___x_1459_ = l_String_toRawSubstring_x27(v___x_1458_);
return v___x_1459_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24(void){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__1));
v___x_1498_ = l_String_toRawSubstring_x27(v___x_1497_);
return v___x_1498_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30(void){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29));
v___x_1511_ = l_String_toRawSubstring_x27(v___x_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(lean_object* v_s_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_){
_start:
{
lean_object* v_msg_1538_; lean_object* v_quotContext_1539_; lean_object* v_currMacroScope_1540_; lean_object* v_ref_1541_; lean_object* v___y_1542_; lean_object* v___x_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
lean_inc(v_s_1534_);
v___x_1557_ = l_Lean_Syntax_getKind(v_s_1534_);
v___x_1558_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16));
v___x_1559_ = lean_name_eq(v___x_1557_, v___x_1558_);
lean_dec(v___x_1557_);
if (v___x_1559_ == 0)
{
lean_object* v_quotContext_1560_; lean_object* v_currMacroScope_1561_; lean_object* v_ref_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v_quotContext_1560_ = lean_ctor_get(v_a_1535_, 1);
v_currMacroScope_1561_ = lean_ctor_get(v_a_1535_, 2);
v_ref_1562_ = lean_ctor_get(v_a_1535_, 5);
v___x_1563_ = l_Lean_SourceInfo_fromRef(v_ref_1562_, v___x_1559_);
v___x_1564_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18));
v___x_1565_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20));
v___x_1566_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21));
lean_inc_n(v___x_1563_, 8);
v___x_1567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1563_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
v___x_1568_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23));
v___x_1569_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
v___x_1570_ = lean_box(0);
lean_inc_n(v_currMacroScope_1561_, 3);
lean_inc_n(v_quotContext_1560_, 3);
v___x_1571_ = l_Lean_addMacroScope(v_quotContext_1560_, v___x_1570_, v_currMacroScope_1561_);
v___x_1572_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27));
v___x_1573_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1563_);
lean_ctor_set(v___x_1573_, 1, v___x_1569_);
lean_ctor_set(v___x_1573_, 2, v___x_1571_);
lean_ctor_set(v___x_1573_, 3, v___x_1572_);
v___x_1574_ = l_Lean_Syntax_node1(v___x_1563_, v___x_1568_, v___x_1573_);
v___x_1575_ = l_Lean_Syntax_node2(v___x_1563_, v___x_1565_, v___x_1567_, v___x_1574_);
v___x_1576_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28));
v___x_1577_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1563_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_1579_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
v___x_1580_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31));
v___x_1581_ = l_Lean_addMacroScope(v_quotContext_1560_, v___x_1580_, v_currMacroScope_1561_);
v___x_1582_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36));
v___x_1583_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1563_);
lean_ctor_set(v___x_1583_, 1, v___x_1579_);
lean_ctor_set(v___x_1583_, 2, v___x_1581_);
lean_ctor_set(v___x_1583_, 3, v___x_1582_);
v___x_1584_ = l_Lean_Syntax_node1(v___x_1563_, v___x_1578_, v___x_1583_);
v___x_1585_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37));
v___x_1586_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1563_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = l_Lean_Syntax_node5(v___x_1563_, v___x_1564_, v___x_1575_, v_s_1534_, v___x_1577_, v___x_1584_, v___x_1586_);
v_msg_1538_ = v___x_1587_;
v_quotContext_1539_ = v_quotContext_1560_;
v_currMacroScope_1540_ = v_currMacroScope_1561_;
v_ref_1541_ = v_ref_1562_;
v___y_1542_ = v_a_1536_;
goto v___jp_1537_;
}
else
{
lean_object* v_quotContext_1588_; lean_object* v_currMacroScope_1589_; lean_object* v_ref_1590_; uint8_t v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v_quotContext_1588_ = lean_ctor_get(v_a_1535_, 1);
v_currMacroScope_1589_ = lean_ctor_get(v_a_1535_, 2);
v_ref_1590_ = lean_ctor_get(v_a_1535_, 5);
v___x_1591_ = 0;
v___x_1592_ = l_Lean_SourceInfo_fromRef(v_ref_1590_, v___x_1591_);
v___x_1593_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39));
v___x_1594_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40));
lean_inc(v___x_1592_);
v___x_1595_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1592_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = l_Lean_Syntax_node2(v___x_1592_, v___x_1593_, v___x_1595_, v_s_1534_);
lean_inc(v_currMacroScope_1589_);
lean_inc(v_quotContext_1588_);
v_msg_1538_ = v___x_1596_;
v_quotContext_1539_ = v_quotContext_1588_;
v_currMacroScope_1540_ = v_currMacroScope_1589_;
v_ref_1541_ = v_ref_1590_;
v___y_1542_ = v_a_1536_;
goto v___jp_1537_;
}
v___jp_1537_:
{
uint8_t v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1543_ = 0;
v___x_1544_ = l_Lean_SourceInfo_fromRef(v_ref_1541_, v___x_1543_);
v___x_1545_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3));
v___x_1546_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5));
v___x_1547_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7);
v___x_1548_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9));
v___x_1549_ = l_Lean_addMacroScope(v_quotContext_1539_, v___x_1548_, v_currMacroScope_1540_);
v___x_1550_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12));
lean_inc_n(v___x_1544_, 3);
v___x_1551_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1544_);
lean_ctor_set(v___x_1551_, 1, v___x_1547_);
lean_ctor_set(v___x_1551_, 2, v___x_1549_);
lean_ctor_set(v___x_1551_, 3, v___x_1550_);
v___x_1552_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_1553_ = l_Lean_Syntax_node1(v___x_1544_, v___x_1552_, v_msg_1538_);
v___x_1554_ = l_Lean_Syntax_node2(v___x_1544_, v___x_1546_, v___x_1551_, v___x_1553_);
v___x_1555_ = l_Lean_Syntax_node1(v___x_1544_, v___x_1545_, v___x_1554_);
v___x_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
lean_ctor_set(v___x_1556_, 1, v___y_1542_);
return v___x_1556_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___boxed(lean_object* v_s_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(v_s_1597_, v_a_1598_, v_a_1599_);
lean_dec_ref(v_a_1598_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(lean_object* v_x_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1644_ = ((lean_object*)(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1));
lean_inc(v_x_1641_);
v___x_1645_ = l_Lean_Syntax_isOfKind(v_x_1641_, v___x_1644_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
lean_dec(v_x_1641_);
v___x_1646_ = lean_box(1);
v___x_1647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
lean_ctor_set(v___x_1647_, 1, v_a_1643_);
return v___x_1647_;
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v_a_1651_; lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
v___x_1648_ = lean_unsigned_to_nat(1u);
v___x_1649_ = l_Lean_Syntax_getArg(v_x_1641_, v___x_1648_);
lean_dec(v_x_1641_);
v___x_1650_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(v___x_1649_, v_a_1642_, v_a_1643_);
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
v_a_1652_ = lean_ctor_get(v___x_1650_, 1);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1650_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_inc(v_a_1651_);
lean_dec(v___x_1650_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1651_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1___boxed(lean_object* v_x_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(v_x_1660_, v_a_1661_, v_a_1662_);
lean_dec_ref(v_a_1661_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue(lean_object* v_msg_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v___x_1672_; lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1692_; 
v___x_1672_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1665_);
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1692_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1672_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1692_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
uint8_t v___x_1677_; 
v___x_1677_ = lean_unbox(v_a_1673_);
lean_dec(v_a_1673_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1680_; 
lean_dec_ref(v_msg_1664_);
v___x_1678_ = lean_box(0);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v___x_1678_);
v___x_1680_ = v___x_1675_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
else
{
lean_object* v_options_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; uint8_t v___x_1686_; 
v_options_1682_ = lean_ctor_get(v_a_1669_, 2);
v___x_1683_ = l_Lean_KVMap_instValueBool;
v___x_1684_ = l_Lean_Meta_Sym_sym_debug;
v___x_1685_ = l_Lean_Option_get___redArg(v___x_1683_, v_options_1682_, v___x_1684_);
v___x_1686_ = lean_unbox(v___x_1685_);
lean_dec(v___x_1685_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; lean_object* v___x_1689_; 
lean_dec_ref(v_msg_1664_);
v___x_1687_ = lean_box(0);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v___x_1687_);
v___x_1689_ = v___x_1675_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
else
{
lean_object* v___x_1691_; 
lean_del_object(v___x_1675_);
v___x_1691_ = l_Lean_Meta_Sym_reportIssue(v_msg_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_);
return v___x_1691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue___boxed(lean_object* v_msg_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_Meta_Sym_reportDbgIssue(v_msg_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
lean_dec(v_a_1697_);
lean_dec_ref(v_a_1696_);
lean_dec(v_a_1695_);
lean_dec_ref(v_a_1694_);
return v_res_1701_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1(void){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0));
v___x_1704_ = l_String_toRawSubstring_x27(v___x_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro(lean_object* v_s_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v_msg_1724_; lean_object* v_quotContext_1725_; lean_object* v_currMacroScope_1726_; lean_object* v_ref_1727_; lean_object* v___y_1728_; lean_object* v___x_1743_; lean_object* v___x_1744_; uint8_t v___x_1745_; 
lean_inc(v_s_1720_);
v___x_1743_ = l_Lean_Syntax_getKind(v_s_1720_);
v___x_1744_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16));
v___x_1745_ = lean_name_eq(v___x_1743_, v___x_1744_);
lean_dec(v___x_1743_);
if (v___x_1745_ == 0)
{
lean_object* v_quotContext_1746_; lean_object* v_currMacroScope_1747_; lean_object* v_ref_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v_quotContext_1746_ = lean_ctor_get(v_a_1721_, 1);
v_currMacroScope_1747_ = lean_ctor_get(v_a_1721_, 2);
v_ref_1748_ = lean_ctor_get(v_a_1721_, 5);
v___x_1749_ = l_Lean_SourceInfo_fromRef(v_ref_1748_, v___x_1745_);
v___x_1750_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18));
v___x_1751_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20));
v___x_1752_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21));
lean_inc_n(v___x_1749_, 8);
v___x_1753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1749_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
v___x_1754_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23));
v___x_1755_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
v___x_1756_ = lean_box(0);
lean_inc_n(v_currMacroScope_1747_, 3);
lean_inc_n(v_quotContext_1746_, 3);
v___x_1757_ = l_Lean_addMacroScope(v_quotContext_1746_, v___x_1756_, v_currMacroScope_1747_);
v___x_1758_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27));
v___x_1759_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1749_);
lean_ctor_set(v___x_1759_, 1, v___x_1755_);
lean_ctor_set(v___x_1759_, 2, v___x_1757_);
lean_ctor_set(v___x_1759_, 3, v___x_1758_);
v___x_1760_ = l_Lean_Syntax_node1(v___x_1749_, v___x_1754_, v___x_1759_);
v___x_1761_ = l_Lean_Syntax_node2(v___x_1749_, v___x_1751_, v___x_1753_, v___x_1760_);
v___x_1762_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28));
v___x_1763_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1749_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_1765_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
v___x_1766_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31));
v___x_1767_ = l_Lean_addMacroScope(v_quotContext_1746_, v___x_1766_, v_currMacroScope_1747_);
v___x_1768_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36));
v___x_1769_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1749_);
lean_ctor_set(v___x_1769_, 1, v___x_1765_);
lean_ctor_set(v___x_1769_, 2, v___x_1767_);
lean_ctor_set(v___x_1769_, 3, v___x_1768_);
v___x_1770_ = l_Lean_Syntax_node1(v___x_1749_, v___x_1764_, v___x_1769_);
v___x_1771_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37));
v___x_1772_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1749_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = l_Lean_Syntax_node5(v___x_1749_, v___x_1750_, v___x_1761_, v_s_1720_, v___x_1763_, v___x_1770_, v___x_1772_);
v_msg_1724_ = v___x_1773_;
v_quotContext_1725_ = v_quotContext_1746_;
v_currMacroScope_1726_ = v_currMacroScope_1747_;
v_ref_1727_ = v_ref_1748_;
v___y_1728_ = v_a_1722_;
goto v___jp_1723_;
}
else
{
lean_object* v_quotContext_1774_; lean_object* v_currMacroScope_1775_; lean_object* v_ref_1776_; uint8_t v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v_quotContext_1774_ = lean_ctor_get(v_a_1721_, 1);
v_currMacroScope_1775_ = lean_ctor_get(v_a_1721_, 2);
v_ref_1776_ = lean_ctor_get(v_a_1721_, 5);
v___x_1777_ = 0;
v___x_1778_ = l_Lean_SourceInfo_fromRef(v_ref_1776_, v___x_1777_);
v___x_1779_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39));
v___x_1780_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40));
lean_inc(v___x_1778_);
v___x_1781_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1778_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = l_Lean_Syntax_node2(v___x_1778_, v___x_1779_, v___x_1781_, v_s_1720_);
lean_inc(v_currMacroScope_1775_);
lean_inc(v_quotContext_1774_);
v_msg_1724_ = v___x_1782_;
v_quotContext_1725_ = v_quotContext_1774_;
v_currMacroScope_1726_ = v_currMacroScope_1775_;
v_ref_1727_ = v_ref_1776_;
v___y_1728_ = v_a_1722_;
goto v___jp_1723_;
}
v___jp_1723_:
{
uint8_t v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1729_ = 0;
v___x_1730_ = l_Lean_SourceInfo_fromRef(v_ref_1727_, v___x_1729_);
v___x_1731_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3));
v___x_1732_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5));
v___x_1733_ = lean_obj_once(&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1, &l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1_once, _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1);
v___x_1734_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3));
v___x_1735_ = l_Lean_addMacroScope(v_quotContext_1725_, v___x_1734_, v_currMacroScope_1726_);
v___x_1736_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6));
lean_inc_n(v___x_1730_, 3);
v___x_1737_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1730_);
lean_ctor_set(v___x_1737_, 1, v___x_1733_);
lean_ctor_set(v___x_1737_, 2, v___x_1735_);
lean_ctor_set(v___x_1737_, 3, v___x_1736_);
v___x_1738_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_1739_ = l_Lean_Syntax_node1(v___x_1730_, v___x_1738_, v_msg_1724_);
v___x_1740_ = l_Lean_Syntax_node2(v___x_1730_, v___x_1732_, v___x_1737_, v___x_1739_);
v___x_1741_ = l_Lean_Syntax_node1(v___x_1730_, v___x_1731_, v___x_1740_);
v___x_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
lean_ctor_set(v___x_1742_, 1, v___y_1728_);
return v___x_1742_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___boxed(lean_object* v_s_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v_s_1783_, v_a_1784_, v_a_1785_);
lean_dec_ref(v_a_1784_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(lean_object* v_x_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v___x_1808_; uint8_t v___x_1809_; 
v___x_1808_ = ((lean_object*)(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1));
lean_inc(v_x_1805_);
v___x_1809_ = l_Lean_Syntax_isOfKind(v_x_1805_, v___x_1808_);
if (v___x_1809_ == 0)
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_dec(v_x_1805_);
v___x_1810_ = lean_box(1);
v___x_1811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
lean_ctor_set(v___x_1811_, 1, v_a_1807_);
return v___x_1811_;
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v_a_1815_; lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
v___x_1812_ = lean_unsigned_to_nat(1u);
v___x_1813_ = l_Lean_Syntax_getArg(v_x_1805_, v___x_1812_);
lean_dec(v_x_1805_);
v___x_1814_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v___x_1813_, v_a_1806_, v_a_1807_);
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_a_1816_ = lean_ctor_get(v___x_1814_, 1);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1818_ = v___x_1814_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1815_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v_a_1816_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1___boxed(lean_object* v_x_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(v_x_1824_, v_a_1825_, v_a_1826_);
lean_dec_ref(v_a_1825_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg(lean_object* v_a_1828_){
_start:
{
lean_object* v___x_1830_; lean_object* v_issues_1831_; lean_object* v___x_1832_; 
v___x_1830_ = lean_st_ref_get(v_a_1828_);
v_issues_1831_ = lean_ctor_get(v___x_1830_, 8);
lean_inc(v_issues_1831_);
lean_dec(v___x_1830_);
v___x_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1832_, 0, v_issues_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg___boxed(lean_object* v_a_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_1833_);
lean_dec(v_a_1833_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues(lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_1837_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___boxed(lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_Meta_Sym_getIssues(v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_);
lean_dec(v_a_1849_);
lean_dec_ref(v_a_1848_);
lean_dec(v_a_1847_);
lean_dec_ref(v_a_1846_);
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1844_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(lean_object* v_a_1852_, lean_object* v_issues_1853_, lean_object* v_a_x3f_1854_){
_start:
{
lean_object* v___x_1856_; lean_object* v_share_1857_; lean_object* v_maxFVar_1858_; lean_object* v_proofInstInfo_1859_; lean_object* v_inferType_1860_; lean_object* v_getLevel_1861_; lean_object* v_congrInfo_1862_; lean_object* v_defEqI_1863_; lean_object* v_extensions_1864_; lean_object* v_issues_1865_; lean_object* v_canon_1866_; uint8_t v_debug_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1878_; 
v___x_1856_ = lean_st_ref_take(v_a_1852_);
v_share_1857_ = lean_ctor_get(v___x_1856_, 0);
v_maxFVar_1858_ = lean_ctor_get(v___x_1856_, 1);
v_proofInstInfo_1859_ = lean_ctor_get(v___x_1856_, 2);
v_inferType_1860_ = lean_ctor_get(v___x_1856_, 3);
v_getLevel_1861_ = lean_ctor_get(v___x_1856_, 4);
v_congrInfo_1862_ = lean_ctor_get(v___x_1856_, 5);
v_defEqI_1863_ = lean_ctor_get(v___x_1856_, 6);
v_extensions_1864_ = lean_ctor_get(v___x_1856_, 7);
v_issues_1865_ = lean_ctor_get(v___x_1856_, 8);
v_canon_1866_ = lean_ctor_get(v___x_1856_, 9);
v_debug_1867_ = lean_ctor_get_uint8(v___x_1856_, sizeof(void*)*10);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1869_ = v___x_1856_;
v_isShared_1870_ = v_isSharedCheck_1878_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_canon_1866_);
lean_inc(v_issues_1865_);
lean_inc(v_extensions_1864_);
lean_inc(v_defEqI_1863_);
lean_inc(v_congrInfo_1862_);
lean_inc(v_getLevel_1861_);
lean_inc(v_inferType_1860_);
lean_inc(v_proofInstInfo_1859_);
lean_inc(v_maxFVar_1858_);
lean_inc(v_share_1857_);
lean_dec(v___x_1856_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1878_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1871_; lean_object* v___x_1873_; 
v___x_1871_ = l_List_appendTR___redArg(v_issues_1865_, v_issues_1853_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 8, v___x_1871_);
v___x_1873_ = v___x_1869_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_share_1857_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v_maxFVar_1858_);
lean_ctor_set(v_reuseFailAlloc_1877_, 2, v_proofInstInfo_1859_);
lean_ctor_set(v_reuseFailAlloc_1877_, 3, v_inferType_1860_);
lean_ctor_set(v_reuseFailAlloc_1877_, 4, v_getLevel_1861_);
lean_ctor_set(v_reuseFailAlloc_1877_, 5, v_congrInfo_1862_);
lean_ctor_set(v_reuseFailAlloc_1877_, 6, v_defEqI_1863_);
lean_ctor_set(v_reuseFailAlloc_1877_, 7, v_extensions_1864_);
lean_ctor_set(v_reuseFailAlloc_1877_, 8, v___x_1871_);
lean_ctor_set(v_reuseFailAlloc_1877_, 9, v_canon_1866_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, sizeof(void*)*10, v_debug_1867_);
v___x_1873_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1874_ = lean_st_ref_set(v_a_1852_, v___x_1873_);
v___x_1875_ = lean_box(0);
v___x_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
return v___x_1876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0___boxed(lean_object* v_a_1879_, lean_object* v_issues_1880_, lean_object* v_a_x3f_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_1879_, v_issues_1880_, v_a_x3f_1881_);
lean_dec(v_a_x3f_1881_);
lean_dec(v_a_1879_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg(lean_object* v_x_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v_share_1894_; lean_object* v_maxFVar_1895_; lean_object* v_proofInstInfo_1896_; lean_object* v_inferType_1897_; lean_object* v_getLevel_1898_; lean_object* v_congrInfo_1899_; lean_object* v_defEqI_1900_; lean_object* v_extensions_1901_; lean_object* v_canon_1902_; uint8_t v_debug_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1942_; 
v___x_1892_ = lean_st_ref_get(v_a_1886_);
v___x_1893_ = lean_st_ref_take(v_a_1886_);
v_share_1894_ = lean_ctor_get(v___x_1893_, 0);
v_maxFVar_1895_ = lean_ctor_get(v___x_1893_, 1);
v_proofInstInfo_1896_ = lean_ctor_get(v___x_1893_, 2);
v_inferType_1897_ = lean_ctor_get(v___x_1893_, 3);
v_getLevel_1898_ = lean_ctor_get(v___x_1893_, 4);
v_congrInfo_1899_ = lean_ctor_get(v___x_1893_, 5);
v_defEqI_1900_ = lean_ctor_get(v___x_1893_, 6);
v_extensions_1901_ = lean_ctor_get(v___x_1893_, 7);
v_canon_1902_ = lean_ctor_get(v___x_1893_, 9);
v_debug_1903_ = lean_ctor_get_uint8(v___x_1893_, sizeof(void*)*10);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1942_ == 0)
{
lean_object* v_unused_1943_; 
v_unused_1943_ = lean_ctor_get(v___x_1893_, 8);
lean_dec(v_unused_1943_);
v___x_1905_ = v___x_1893_;
v_isShared_1906_ = v_isSharedCheck_1942_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_canon_1902_);
lean_inc(v_extensions_1901_);
lean_inc(v_defEqI_1900_);
lean_inc(v_congrInfo_1899_);
lean_inc(v_getLevel_1898_);
lean_inc(v_inferType_1897_);
lean_inc(v_proofInstInfo_1896_);
lean_inc(v_maxFVar_1895_);
lean_inc(v_share_1894_);
lean_dec(v___x_1893_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1942_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1907_ = lean_box(0);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 8, v___x_1907_);
v___x_1909_ = v___x_1905_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_share_1894_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v_maxFVar_1895_);
lean_ctor_set(v_reuseFailAlloc_1941_, 2, v_proofInstInfo_1896_);
lean_ctor_set(v_reuseFailAlloc_1941_, 3, v_inferType_1897_);
lean_ctor_set(v_reuseFailAlloc_1941_, 4, v_getLevel_1898_);
lean_ctor_set(v_reuseFailAlloc_1941_, 5, v_congrInfo_1899_);
lean_ctor_set(v_reuseFailAlloc_1941_, 6, v_defEqI_1900_);
lean_ctor_set(v_reuseFailAlloc_1941_, 7, v_extensions_1901_);
lean_ctor_set(v_reuseFailAlloc_1941_, 8, v___x_1907_);
lean_ctor_set(v_reuseFailAlloc_1941_, 9, v_canon_1902_);
lean_ctor_set_uint8(v_reuseFailAlloc_1941_, sizeof(void*)*10, v_debug_1903_);
v___x_1909_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1910_; lean_object* v_issues_1911_; lean_object* v_r_1912_; 
v___x_1910_ = lean_st_ref_set(v_a_1886_, v___x_1909_);
v_issues_1911_ = lean_ctor_get(v___x_1892_, 8);
lean_inc(v_issues_1911_);
lean_dec(v___x_1892_);
lean_inc(v_a_1890_);
lean_inc_ref(v_a_1889_);
lean_inc(v_a_1888_);
lean_inc_ref(v_a_1887_);
lean_inc(v_a_1886_);
lean_inc_ref(v_a_1885_);
v_r_1912_ = lean_apply_7(v_x_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, lean_box(0));
if (lean_obj_tag(v_r_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1929_; 
v_a_1913_ = lean_ctor_get(v_r_1912_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_r_1912_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1915_ = v_r_1912_;
v_isShared_1916_ = v_isSharedCheck_1929_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v_r_1912_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1929_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
lean_inc(v_a_1913_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set_tag(v___x_1915_, 1);
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
v___x_1919_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_1886_, v_issues_1911_, v___x_1918_);
lean_dec_ref(v___x_1918_);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1926_ == 0)
{
lean_object* v_unused_1927_; 
v_unused_1927_ = lean_ctor_get(v___x_1919_, 0);
lean_dec(v_unused_1927_);
v___x_1921_ = v___x_1919_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_dec(v___x_1919_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v_a_1913_);
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1913_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
v_a_1930_ = lean_ctor_get(v_r_1912_, 0);
lean_inc(v_a_1930_);
lean_dec_ref_known(v_r_1912_, 1);
v___x_1931_ = lean_box(0);
v___x_1932_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_1886_, v_issues_1911_, v___x_1931_);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1939_ == 0)
{
lean_object* v_unused_1940_; 
v_unused_1940_ = lean_ctor_get(v___x_1932_, 0);
lean_dec(v_unused_1940_);
v___x_1934_ = v___x_1932_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_dec(v___x_1932_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
lean_ctor_set_tag(v___x_1934_, 1);
lean_ctor_set(v___x_1934_, 0, v_a_1930_);
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1930_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___boxed(lean_object* v_x_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
lean_dec(v_a_1948_);
lean_dec_ref(v_a_1947_);
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext(lean_object* v_00_u03b1_1953_, lean_object* v_x_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___boxed(lean_object* v_00_u03b1_1963_, lean_object* v_x_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_Meta_Sym_withNewIssueContext(v_00_u03b1_1963_, v_x_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_);
lean_dec(v_a_1970_);
lean_dec_ref(v_a_1969_);
lean_dec(v_a_1968_);
lean_dec_ref(v_a_1967_);
lean_dec(v_a_1966_);
lean_dec_ref(v_a_1965_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1973_, lean_object* v_vals_1974_, lean_object* v_i_1975_, lean_object* v_k_1976_){
_start:
{
uint8_t v___y_1978_; lean_object* v___x_1984_; uint8_t v___x_1985_; 
v___x_1984_ = lean_array_get_size(v_keys_1973_);
v___x_1985_ = lean_nat_dec_lt(v_i_1975_, v___x_1984_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1986_; 
lean_dec(v_i_1975_);
v___x_1986_ = lean_box(0);
return v___x_1986_;
}
else
{
lean_object* v_fst_1987_; lean_object* v_snd_1988_; lean_object* v_k_x27_1989_; lean_object* v_fst_1990_; lean_object* v_snd_1991_; uint8_t v___x_1992_; 
v_fst_1987_ = lean_ctor_get(v_k_1976_, 0);
v_snd_1988_ = lean_ctor_get(v_k_1976_, 1);
v_k_x27_1989_ = lean_array_fget_borrowed(v_keys_1973_, v_i_1975_);
v_fst_1990_ = lean_ctor_get(v_k_x27_1989_, 0);
v_snd_1991_ = lean_ctor_get(v_k_x27_1989_, 1);
v___x_1992_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_1987_, v_fst_1990_);
if (v___x_1992_ == 0)
{
v___y_1978_ = v___x_1992_;
goto v___jp_1977_;
}
else
{
uint8_t v___x_1993_; 
v___x_1993_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_snd_1988_, v_snd_1991_);
v___y_1978_ = v___x_1993_;
goto v___jp_1977_;
}
}
v___jp_1977_:
{
if (v___y_1978_ == 0)
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = lean_unsigned_to_nat(1u);
v___x_1980_ = lean_nat_add(v_i_1975_, v___x_1979_);
lean_dec(v_i_1975_);
v_i_1975_ = v___x_1980_;
goto _start;
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = lean_array_fget_borrowed(v_vals_1974_, v_i_1975_);
lean_dec(v_i_1975_);
lean_inc(v___x_1982_);
v___x_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
return v___x_1983_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1994_, lean_object* v_vals_1995_, lean_object* v_i_1996_, lean_object* v_k_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_1994_, v_vals_1995_, v_i_1996_, v_k_1997_);
lean_dec_ref(v_k_1997_);
lean_dec_ref(v_vals_1995_);
lean_dec_ref(v_keys_1994_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(lean_object* v_x_1999_, size_t v_x_2000_, lean_object* v_x_2001_){
_start:
{
if (lean_obj_tag(v_x_1999_) == 0)
{
lean_object* v_es_2002_; lean_object* v___x_2003_; size_t v___x_2004_; size_t v___x_2005_; lean_object* v_j_2006_; lean_object* v___x_2007_; 
v_es_2002_ = lean_ctor_get(v_x_1999_, 0);
v___x_2003_ = lean_box(2);
v___x_2004_ = ((size_t)31ULL);
v___x_2005_ = lean_usize_land(v_x_2000_, v___x_2004_);
v_j_2006_ = lean_usize_to_nat(v___x_2005_);
v___x_2007_ = lean_array_get_borrowed(v___x_2003_, v_es_2002_, v_j_2006_);
lean_dec(v_j_2006_);
switch(lean_obj_tag(v___x_2007_))
{
case 0:
{
lean_object* v_key_2008_; lean_object* v_val_2009_; uint8_t v___y_2011_; lean_object* v_fst_2014_; lean_object* v_snd_2015_; lean_object* v_fst_2016_; lean_object* v_snd_2017_; uint8_t v___x_2018_; 
v_key_2008_ = lean_ctor_get(v___x_2007_, 0);
v_val_2009_ = lean_ctor_get(v___x_2007_, 1);
v_fst_2014_ = lean_ctor_get(v_x_2001_, 0);
v_snd_2015_ = lean_ctor_get(v_x_2001_, 1);
v_fst_2016_ = lean_ctor_get(v_key_2008_, 0);
v_snd_2017_ = lean_ctor_get(v_key_2008_, 1);
v___x_2018_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_2014_, v_fst_2016_);
if (v___x_2018_ == 0)
{
v___y_2011_ = v___x_2018_;
goto v___jp_2010_;
}
else
{
uint8_t v___x_2019_; 
v___x_2019_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_snd_2015_, v_snd_2017_);
v___y_2011_ = v___x_2019_;
goto v___jp_2010_;
}
v___jp_2010_:
{
if (v___y_2011_ == 0)
{
lean_object* v___x_2012_; 
v___x_2012_ = lean_box(0);
return v___x_2012_;
}
else
{
lean_object* v___x_2013_; 
lean_inc(v_val_2009_);
v___x_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2013_, 0, v_val_2009_);
return v___x_2013_;
}
}
}
case 1:
{
lean_object* v_node_2020_; size_t v___x_2021_; size_t v___x_2022_; 
v_node_2020_ = lean_ctor_get(v___x_2007_, 0);
v___x_2021_ = ((size_t)5ULL);
v___x_2022_ = lean_usize_shift_right(v_x_2000_, v___x_2021_);
v_x_1999_ = v_node_2020_;
v_x_2000_ = v___x_2022_;
goto _start;
}
default: 
{
lean_object* v___x_2024_; 
v___x_2024_ = lean_box(0);
return v___x_2024_;
}
}
}
else
{
lean_object* v_ks_2025_; lean_object* v_vs_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v_ks_2025_ = lean_ctor_get(v_x_1999_, 0);
v_vs_2026_ = lean_ctor_get(v_x_1999_, 1);
v___x_2027_ = lean_unsigned_to_nat(0u);
v___x_2028_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_ks_2025_, v_vs_2026_, v___x_2027_, v_x_2001_);
return v___x_2028_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg___boxed(lean_object* v_x_2029_, lean_object* v_x_2030_, lean_object* v_x_2031_){
_start:
{
size_t v_x_2646__boxed_2032_; lean_object* v_res_2033_; 
v_x_2646__boxed_2032_ = lean_unbox_usize(v_x_2030_);
lean_dec(v_x_2030_);
v_res_2033_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_2029_, v_x_2646__boxed_2032_, v_x_2031_);
lean_dec_ref(v_x_2031_);
lean_dec_ref(v_x_2029_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(lean_object* v_x_2034_, lean_object* v_x_2035_){
_start:
{
lean_object* v_fst_2036_; lean_object* v_snd_2037_; uint64_t v___x_2038_; uint64_t v___x_2039_; uint64_t v___x_2040_; size_t v___x_2041_; lean_object* v___x_2042_; 
v_fst_2036_ = lean_ctor_get(v_x_2035_, 0);
v_snd_2037_ = lean_ctor_get(v_x_2035_, 1);
v___x_2038_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_2036_);
v___x_2039_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_snd_2037_);
v___x_2040_ = lean_uint64_mix_hash(v___x_2038_, v___x_2039_);
v___x_2041_ = lean_uint64_to_usize(v___x_2040_);
v___x_2042_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_2034_, v___x_2041_, v_x_2035_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg___boxed(lean_object* v_x_2043_, lean_object* v_x_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_2043_, v_x_2044_);
lean_dec_ref(v_x_2044_);
lean_dec_ref(v_x_2043_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2046_, lean_object* v_x_2047_, lean_object* v_x_2048_, lean_object* v_x_2049_){
_start:
{
lean_object* v_ks_2050_; lean_object* v_vs_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2080_; 
v_ks_2050_ = lean_ctor_get(v_x_2046_, 0);
v_vs_2051_ = lean_ctor_get(v_x_2046_, 1);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_x_2046_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2053_ = v_x_2046_;
v_isShared_2054_ = v_isSharedCheck_2080_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_vs_2051_);
lean_inc(v_ks_2050_);
lean_dec(v_x_2046_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2080_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
uint8_t v___y_2056_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v___x_2068_ = lean_array_get_size(v_ks_2050_);
v___x_2069_ = lean_nat_dec_lt(v_x_2047_, v___x_2068_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
lean_del_object(v___x_2053_);
lean_dec(v_x_2047_);
v___x_2070_ = lean_array_push(v_ks_2050_, v_x_2048_);
v___x_2071_ = lean_array_push(v_vs_2051_, v_x_2049_);
v___x_2072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2070_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
return v___x_2072_;
}
else
{
lean_object* v_fst_2073_; lean_object* v_snd_2074_; lean_object* v_k_x27_2075_; lean_object* v_fst_2076_; lean_object* v_snd_2077_; uint8_t v___x_2078_; 
v_fst_2073_ = lean_ctor_get(v_x_2048_, 0);
v_snd_2074_ = lean_ctor_get(v_x_2048_, 1);
v_k_x27_2075_ = lean_array_fget_borrowed(v_ks_2050_, v_x_2047_);
v_fst_2076_ = lean_ctor_get(v_k_x27_2075_, 0);
v_snd_2077_ = lean_ctor_get(v_k_x27_2075_, 1);
v___x_2078_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_2073_, v_fst_2076_);
if (v___x_2078_ == 0)
{
v___y_2056_ = v___x_2078_;
goto v___jp_2055_;
}
else
{
uint8_t v___x_2079_; 
v___x_2079_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_snd_2074_, v_snd_2077_);
v___y_2056_ = v___x_2079_;
goto v___jp_2055_;
}
}
v___jp_2055_:
{
if (v___y_2056_ == 0)
{
lean_object* v___x_2058_; 
if (v_isShared_2054_ == 0)
{
v___x_2058_ = v___x_2053_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_ks_2050_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v_vs_2051_);
v___x_2058_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = lean_unsigned_to_nat(1u);
v___x_2060_ = lean_nat_add(v_x_2047_, v___x_2059_);
lean_dec(v_x_2047_);
v_x_2046_ = v___x_2058_;
v_x_2047_ = v___x_2060_;
goto _start;
}
}
else
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2066_; 
v___x_2063_ = lean_array_fset(v_ks_2050_, v_x_2047_, v_x_2048_);
v___x_2064_ = lean_array_fset(v_vs_2051_, v_x_2047_, v_x_2049_);
lean_dec(v_x_2047_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 1, v___x_2064_);
lean_ctor_set(v___x_2053_, 0, v___x_2063_);
v___x_2066_ = v___x_2053_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(lean_object* v_n_2081_, lean_object* v_k_2082_, lean_object* v_v_2083_){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = lean_unsigned_to_nat(0u);
v___x_2085_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_n_2081_, v___x_2084_, v_k_2082_, v_v_2083_);
return v___x_2085_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(lean_object* v_x_2087_, size_t v_x_2088_, size_t v_x_2089_, lean_object* v_x_2090_, lean_object* v_x_2091_){
_start:
{
if (lean_obj_tag(v_x_2087_) == 0)
{
lean_object* v_es_2092_; size_t v___x_2093_; size_t v___x_2094_; lean_object* v_j_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; 
v_es_2092_ = lean_ctor_get(v_x_2087_, 0);
v___x_2093_ = ((size_t)31ULL);
v___x_2094_ = lean_usize_land(v_x_2088_, v___x_2093_);
v_j_2095_ = lean_usize_to_nat(v___x_2094_);
v___x_2096_ = lean_array_get_size(v_es_2092_);
v___x_2097_ = lean_nat_dec_lt(v_j_2095_, v___x_2096_);
if (v___x_2097_ == 0)
{
lean_dec(v_j_2095_);
lean_dec(v_x_2091_);
lean_dec_ref(v_x_2090_);
return v_x_2087_;
}
else
{
lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2143_; 
lean_inc_ref(v_es_2092_);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_x_2087_);
if (v_isSharedCheck_2143_ == 0)
{
lean_object* v_unused_2144_; 
v_unused_2144_ = lean_ctor_get(v_x_2087_, 0);
lean_dec(v_unused_2144_);
v___x_2099_ = v_x_2087_;
v_isShared_2100_ = v_isSharedCheck_2143_;
goto v_resetjp_2098_;
}
else
{
lean_dec(v_x_2087_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2143_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v_v_2101_; lean_object* v___x_2102_; lean_object* v_xs_x27_2103_; lean_object* v___y_2105_; 
v_v_2101_ = lean_array_fget(v_es_2092_, v_j_2095_);
v___x_2102_ = lean_box(0);
v_xs_x27_2103_ = lean_array_fset(v_es_2092_, v_j_2095_, v___x_2102_);
switch(lean_obj_tag(v_v_2101_))
{
case 0:
{
lean_object* v_key_2110_; lean_object* v_val_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2128_; 
v_key_2110_ = lean_ctor_get(v_v_2101_, 0);
v_val_2111_ = lean_ctor_get(v_v_2101_, 1);
v_isSharedCheck_2128_ = !lean_is_exclusive(v_v_2101_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2113_ = v_v_2101_;
v_isShared_2114_ = v_isSharedCheck_2128_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_val_2111_);
lean_inc(v_key_2110_);
lean_dec(v_v_2101_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2128_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
uint8_t v___y_2116_; lean_object* v_fst_2122_; lean_object* v_snd_2123_; lean_object* v_fst_2124_; lean_object* v_snd_2125_; uint8_t v___x_2126_; 
v_fst_2122_ = lean_ctor_get(v_x_2090_, 0);
v_snd_2123_ = lean_ctor_get(v_x_2090_, 1);
v_fst_2124_ = lean_ctor_get(v_key_2110_, 0);
v_snd_2125_ = lean_ctor_get(v_key_2110_, 1);
v___x_2126_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_2122_, v_fst_2124_);
if (v___x_2126_ == 0)
{
v___y_2116_ = v___x_2126_;
goto v___jp_2115_;
}
else
{
uint8_t v___x_2127_; 
v___x_2127_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_snd_2123_, v_snd_2125_);
v___y_2116_ = v___x_2127_;
goto v___jp_2115_;
}
v___jp_2115_:
{
if (v___y_2116_ == 0)
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
lean_del_object(v___x_2113_);
v___x_2117_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2110_, v_val_2111_, v_x_2090_, v_x_2091_);
v___x_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
v___y_2105_ = v___x_2118_;
goto v___jp_2104_;
}
else
{
lean_object* v___x_2120_; 
lean_dec(v_val_2111_);
lean_dec(v_key_2110_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 1, v_x_2091_);
lean_ctor_set(v___x_2113_, 0, v_x_2090_);
v___x_2120_ = v___x_2113_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_x_2090_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v_x_2091_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
v___y_2105_ = v___x_2120_;
goto v___jp_2104_;
}
}
}
}
}
case 1:
{
lean_object* v_node_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2141_; 
v_node_2129_ = lean_ctor_get(v_v_2101_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_v_2101_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2131_ = v_v_2101_;
v_isShared_2132_ = v_isSharedCheck_2141_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_node_2129_);
lean_dec(v_v_2101_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2141_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
size_t v___x_2133_; size_t v___x_2134_; size_t v___x_2135_; size_t v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2139_; 
v___x_2133_ = ((size_t)5ULL);
v___x_2134_ = lean_usize_shift_right(v_x_2088_, v___x_2133_);
v___x_2135_ = ((size_t)1ULL);
v___x_2136_ = lean_usize_add(v_x_2089_, v___x_2135_);
v___x_2137_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_node_2129_, v___x_2134_, v___x_2136_, v_x_2090_, v_x_2091_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 0, v___x_2137_);
v___x_2139_ = v___x_2131_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
v___y_2105_ = v___x_2139_;
goto v___jp_2104_;
}
}
}
default: 
{
lean_object* v___x_2142_; 
v___x_2142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2142_, 0, v_x_2090_);
lean_ctor_set(v___x_2142_, 1, v_x_2091_);
v___y_2105_ = v___x_2142_;
goto v___jp_2104_;
}
}
v___jp_2104_:
{
lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2106_ = lean_array_fset(v_xs_x27_2103_, v_j_2095_, v___y_2105_);
lean_dec(v_j_2095_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 0, v___x_2106_);
v___x_2108_ = v___x_2099_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
}
else
{
lean_object* v_ks_2145_; lean_object* v_vs_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2166_; 
v_ks_2145_ = lean_ctor_get(v_x_2087_, 0);
v_vs_2146_ = lean_ctor_get(v_x_2087_, 1);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_x_2087_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2148_ = v_x_2087_;
v_isShared_2149_ = v_isSharedCheck_2166_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_vs_2146_);
lean_inc(v_ks_2145_);
lean_dec(v_x_2087_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2166_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_ks_2145_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_vs_2146_);
v___x_2151_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
lean_object* v_newNode_2152_; uint8_t v___y_2154_; size_t v___x_2160_; uint8_t v___x_2161_; 
v_newNode_2152_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v___x_2151_, v_x_2090_, v_x_2091_);
v___x_2160_ = ((size_t)7ULL);
v___x_2161_ = lean_usize_dec_le(v___x_2160_, v_x_2089_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; lean_object* v___x_2163_; uint8_t v___x_2164_; 
v___x_2162_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2152_);
v___x_2163_ = lean_unsigned_to_nat(4u);
v___x_2164_ = lean_nat_dec_lt(v___x_2162_, v___x_2163_);
lean_dec(v___x_2162_);
v___y_2154_ = v___x_2164_;
goto v___jp_2153_;
}
else
{
v___y_2154_ = v___x_2161_;
goto v___jp_2153_;
}
v___jp_2153_:
{
if (v___y_2154_ == 0)
{
lean_object* v_ks_2155_; lean_object* v_vs_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v_ks_2155_ = lean_ctor_get(v_newNode_2152_, 0);
lean_inc_ref(v_ks_2155_);
v_vs_2156_ = lean_ctor_get(v_newNode_2152_, 1);
lean_inc_ref(v_vs_2156_);
lean_dec_ref(v_newNode_2152_);
v___x_2157_ = lean_unsigned_to_nat(0u);
v___x_2158_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0);
v___x_2159_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_x_2089_, v_ks_2155_, v_vs_2156_, v___x_2157_, v___x_2158_);
lean_dec_ref(v_vs_2156_);
lean_dec_ref(v_ks_2155_);
return v___x_2159_;
}
else
{
return v_newNode_2152_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(size_t v_depth_2167_, lean_object* v_keys_2168_, lean_object* v_vals_2169_, lean_object* v_i_2170_, lean_object* v_entries_2171_){
_start:
{
lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2172_ = lean_array_get_size(v_keys_2168_);
v___x_2173_ = lean_nat_dec_lt(v_i_2170_, v___x_2172_);
if (v___x_2173_ == 0)
{
lean_dec(v_i_2170_);
return v_entries_2171_;
}
else
{
lean_object* v_k_2174_; lean_object* v_fst_2175_; lean_object* v_snd_2176_; lean_object* v_v_2177_; uint64_t v___x_2178_; uint64_t v___x_2179_; uint64_t v___x_2180_; size_t v_h_2181_; size_t v___x_2182_; lean_object* v___x_2183_; size_t v___x_2184_; size_t v___x_2185_; size_t v___x_2186_; size_t v_h_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v_k_2174_ = lean_array_fget_borrowed(v_keys_2168_, v_i_2170_);
v_fst_2175_ = lean_ctor_get(v_k_2174_, 0);
v_snd_2176_ = lean_ctor_get(v_k_2174_, 1);
v_v_2177_ = lean_array_fget_borrowed(v_vals_2169_, v_i_2170_);
v___x_2178_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_2175_);
v___x_2179_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_snd_2176_);
v___x_2180_ = lean_uint64_mix_hash(v___x_2178_, v___x_2179_);
v_h_2181_ = lean_uint64_to_usize(v___x_2180_);
v___x_2182_ = ((size_t)5ULL);
v___x_2183_ = lean_unsigned_to_nat(1u);
v___x_2184_ = ((size_t)1ULL);
v___x_2185_ = lean_usize_sub(v_depth_2167_, v___x_2184_);
v___x_2186_ = lean_usize_mul(v___x_2182_, v___x_2185_);
v_h_2187_ = lean_usize_shift_right(v_h_2181_, v___x_2186_);
v___x_2188_ = lean_nat_add(v_i_2170_, v___x_2183_);
lean_dec(v_i_2170_);
lean_inc(v_v_2177_);
lean_inc(v_k_2174_);
v___x_2189_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_entries_2171_, v_h_2187_, v_depth_2167_, v_k_2174_, v_v_2177_);
v_i_2170_ = v___x_2188_;
v_entries_2171_ = v___x_2189_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_2191_, lean_object* v_keys_2192_, lean_object* v_vals_2193_, lean_object* v_i_2194_, lean_object* v_entries_2195_){
_start:
{
size_t v_depth_boxed_2196_; lean_object* v_res_2197_; 
v_depth_boxed_2196_ = lean_unbox_usize(v_depth_2191_);
lean_dec(v_depth_2191_);
v_res_2197_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_boxed_2196_, v_keys_2192_, v_vals_2193_, v_i_2194_, v_entries_2195_);
lean_dec_ref(v_vals_2193_);
lean_dec_ref(v_keys_2192_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___boxed(lean_object* v_x_2198_, lean_object* v_x_2199_, lean_object* v_x_2200_, lean_object* v_x_2201_, lean_object* v_x_2202_){
_start:
{
size_t v_x_2817__boxed_2203_; size_t v_x_2818__boxed_2204_; lean_object* v_res_2205_; 
v_x_2817__boxed_2203_ = lean_unbox_usize(v_x_2199_);
lean_dec(v_x_2199_);
v_x_2818__boxed_2204_ = lean_unbox_usize(v_x_2200_);
lean_dec(v_x_2200_);
v_res_2205_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_2198_, v_x_2817__boxed_2203_, v_x_2818__boxed_2204_, v_x_2201_, v_x_2202_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(lean_object* v_x_2206_, lean_object* v_x_2207_, lean_object* v_x_2208_){
_start:
{
lean_object* v_fst_2209_; lean_object* v_snd_2210_; uint64_t v___x_2211_; uint64_t v___x_2212_; uint64_t v___x_2213_; size_t v___x_2214_; size_t v___x_2215_; lean_object* v___x_2216_; 
v_fst_2209_ = lean_ctor_get(v_x_2207_, 0);
v_snd_2210_ = lean_ctor_get(v_x_2207_, 1);
v___x_2211_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_2209_);
v___x_2212_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_snd_2210_);
v___x_2213_ = lean_uint64_mix_hash(v___x_2211_, v___x_2212_);
v___x_2214_ = lean_uint64_to_usize(v___x_2213_);
v___x_2215_ = ((size_t)1ULL);
v___x_2216_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_2206_, v___x_2214_, v___x_2215_, v_x_2207_, v_x_2208_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object* v_s_2217_, lean_object* v_t_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_){
_start:
{
lean_object* v___x_2225_; lean_object* v_defEqI_2226_; lean_object* v_key_2227_; lean_object* v___x_2228_; 
v___x_2225_ = lean_st_ref_get(v_a_2219_);
v_defEqI_2226_ = lean_ctor_get(v___x_2225_, 6);
lean_inc_ref(v_defEqI_2226_);
lean_dec(v___x_2225_);
lean_inc_ref(v_t_2218_);
lean_inc_ref(v_s_2217_);
v_key_2227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_2227_, 0, v_s_2217_);
lean_ctor_set(v_key_2227_, 1, v_t_2218_);
v___x_2228_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_defEqI_2226_, v_key_2227_);
lean_dec_ref(v_defEqI_2226_);
if (lean_obj_tag(v___x_2228_) == 1)
{
lean_object* v_val_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
lean_dec_ref_known(v_key_2227_, 2);
lean_dec_ref(v_t_2218_);
lean_dec_ref(v_s_2217_);
v_val_2229_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2231_ = v___x_2228_;
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_val_2229_);
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
lean_ctor_set_tag(v___x_2231_, 0);
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_val_2229_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
else
{
lean_object* v___x_2237_; 
lean_dec(v___x_2228_);
v___x_2237_ = l_Lean_Meta_isDefEqI(v_s_2217_, v_t_2218_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2266_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2240_ = v___x_2237_;
v_isShared_2241_ = v_isSharedCheck_2266_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2237_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2266_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2242_; lean_object* v_share_2243_; lean_object* v_maxFVar_2244_; lean_object* v_proofInstInfo_2245_; lean_object* v_inferType_2246_; lean_object* v_getLevel_2247_; lean_object* v_congrInfo_2248_; lean_object* v_defEqI_2249_; lean_object* v_extensions_2250_; lean_object* v_issues_2251_; lean_object* v_canon_2252_; uint8_t v_debug_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2265_; 
v___x_2242_ = lean_st_ref_take(v_a_2219_);
v_share_2243_ = lean_ctor_get(v___x_2242_, 0);
v_maxFVar_2244_ = lean_ctor_get(v___x_2242_, 1);
v_proofInstInfo_2245_ = lean_ctor_get(v___x_2242_, 2);
v_inferType_2246_ = lean_ctor_get(v___x_2242_, 3);
v_getLevel_2247_ = lean_ctor_get(v___x_2242_, 4);
v_congrInfo_2248_ = lean_ctor_get(v___x_2242_, 5);
v_defEqI_2249_ = lean_ctor_get(v___x_2242_, 6);
v_extensions_2250_ = lean_ctor_get(v___x_2242_, 7);
v_issues_2251_ = lean_ctor_get(v___x_2242_, 8);
v_canon_2252_ = lean_ctor_get(v___x_2242_, 9);
v_debug_2253_ = lean_ctor_get_uint8(v___x_2242_, sizeof(void*)*10);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2255_ = v___x_2242_;
v_isShared_2256_ = v_isSharedCheck_2265_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_canon_2252_);
lean_inc(v_issues_2251_);
lean_inc(v_extensions_2250_);
lean_inc(v_defEqI_2249_);
lean_inc(v_congrInfo_2248_);
lean_inc(v_getLevel_2247_);
lean_inc(v_inferType_2246_);
lean_inc(v_proofInstInfo_2245_);
lean_inc(v_maxFVar_2244_);
lean_inc(v_share_2243_);
lean_dec(v___x_2242_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2265_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2257_; lean_object* v___x_2259_; 
lean_inc(v_a_2238_);
v___x_2257_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_defEqI_2249_, v_key_2227_, v_a_2238_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 6, v___x_2257_);
v___x_2259_ = v___x_2255_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_share_2243_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v_maxFVar_2244_);
lean_ctor_set(v_reuseFailAlloc_2264_, 2, v_proofInstInfo_2245_);
lean_ctor_set(v_reuseFailAlloc_2264_, 3, v_inferType_2246_);
lean_ctor_set(v_reuseFailAlloc_2264_, 4, v_getLevel_2247_);
lean_ctor_set(v_reuseFailAlloc_2264_, 5, v_congrInfo_2248_);
lean_ctor_set(v_reuseFailAlloc_2264_, 6, v___x_2257_);
lean_ctor_set(v_reuseFailAlloc_2264_, 7, v_extensions_2250_);
lean_ctor_set(v_reuseFailAlloc_2264_, 8, v_issues_2251_);
lean_ctor_set(v_reuseFailAlloc_2264_, 9, v_canon_2252_);
lean_ctor_set_uint8(v_reuseFailAlloc_2264_, sizeof(void*)*10, v_debug_2253_);
v___x_2259_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
lean_object* v___x_2260_; lean_object* v___x_2262_; 
v___x_2260_ = lean_st_ref_set(v_a_2219_, v___x_2259_);
if (v_isShared_2241_ == 0)
{
v___x_2262_ = v___x_2240_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2238_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_2227_, 2);
return v___x_2237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg___boxed(lean_object* v_s_2267_, lean_object* v_t_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_2267_, v_t_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
lean_dec(v_a_2273_);
lean_dec_ref(v_a_2272_);
lean_dec(v_a_2271_);
lean_dec_ref(v_a_2270_);
lean_dec(v_a_2269_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI(lean_object* v_s_2276_, lean_object* v_t_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_2276_, v_t_2277_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___boxed(lean_object* v_s_2286_, lean_object* v_t_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lean_Meta_Sym_isDefEqI(v_s_2286_, v_t_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(lean_object* v_00_u03b2_2296_, lean_object* v_x_2297_, lean_object* v_x_2298_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_2297_, v_x_2298_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___boxed(lean_object* v_00_u03b2_2300_, lean_object* v_x_2301_, lean_object* v_x_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(v_00_u03b2_2300_, v_x_2301_, v_x_2302_);
lean_dec_ref(v_x_2302_);
lean_dec_ref(v_x_2301_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1(lean_object* v_00_u03b2_2304_, lean_object* v_x_2305_, lean_object* v_x_2306_, lean_object* v_x_2307_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_x_2305_, v_x_2306_, v_x_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(lean_object* v_00_u03b2_2309_, lean_object* v_x_2310_, size_t v_x_2311_, lean_object* v_x_2312_){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_2310_, v_x_2311_, v_x_2312_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2314_, lean_object* v_x_2315_, lean_object* v_x_2316_, lean_object* v_x_2317_){
_start:
{
size_t v_x_3096__boxed_2318_; lean_object* v_res_2319_; 
v_x_3096__boxed_2318_ = lean_unbox_usize(v_x_2316_);
lean_dec(v_x_2316_);
v_res_2319_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(v_00_u03b2_2314_, v_x_2315_, v_x_3096__boxed_2318_, v_x_2317_);
lean_dec_ref(v_x_2317_);
lean_dec_ref(v_x_2315_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(lean_object* v_00_u03b2_2320_, lean_object* v_x_2321_, size_t v_x_2322_, size_t v_x_2323_, lean_object* v_x_2324_, lean_object* v_x_2325_){
_start:
{
lean_object* v___x_2326_; 
v___x_2326_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_2321_, v_x_2322_, v_x_2323_, v_x_2324_, v_x_2325_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2327_, lean_object* v_x_2328_, lean_object* v_x_2329_, lean_object* v_x_2330_, lean_object* v_x_2331_, lean_object* v_x_2332_){
_start:
{
size_t v_x_3107__boxed_2333_; size_t v_x_3108__boxed_2334_; lean_object* v_res_2335_; 
v_x_3107__boxed_2333_ = lean_unbox_usize(v_x_2329_);
lean_dec(v_x_2329_);
v_x_3108__boxed_2334_ = lean_unbox_usize(v_x_2330_);
lean_dec(v_x_2330_);
v_res_2335_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(v_00_u03b2_2327_, v_x_2328_, v_x_3107__boxed_2333_, v_x_3108__boxed_2334_, v_x_2331_, v_x_2332_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2336_, lean_object* v_keys_2337_, lean_object* v_vals_2338_, lean_object* v_heq_2339_, lean_object* v_i_2340_, lean_object* v_k_2341_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_2337_, v_vals_2338_, v_i_2340_, v_k_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2343_, lean_object* v_keys_2344_, lean_object* v_vals_2345_, lean_object* v_heq_2346_, lean_object* v_i_2347_, lean_object* v_k_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(v_00_u03b2_2343_, v_keys_2344_, v_vals_2345_, v_heq_2346_, v_i_2347_, v_k_2348_);
lean_dec_ref(v_k_2348_);
lean_dec_ref(v_vals_2345_);
lean_dec_ref(v_keys_2344_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2350_, lean_object* v_n_2351_, lean_object* v_k_2352_, lean_object* v_v_2353_){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v_n_2351_, v_k_2352_, v_v_2353_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_2355_, size_t v_depth_2356_, lean_object* v_keys_2357_, lean_object* v_vals_2358_, lean_object* v_heq_2359_, lean_object* v_i_2360_, lean_object* v_entries_2361_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_2356_, v_keys_2357_, v_vals_2358_, v_i_2360_, v_entries_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2363_, lean_object* v_depth_2364_, lean_object* v_keys_2365_, lean_object* v_vals_2366_, lean_object* v_heq_2367_, lean_object* v_i_2368_, lean_object* v_entries_2369_){
_start:
{
size_t v_depth_boxed_2370_; lean_object* v_res_2371_; 
v_depth_boxed_2370_ = lean_unbox_usize(v_depth_2364_);
lean_dec(v_depth_2364_);
v_res_2371_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(v_00_u03b2_2363_, v_depth_boxed_2370_, v_keys_2365_, v_vals_2366_, v_heq_2367_, v_i_2368_, v_entries_2369_);
lean_dec_ref(v_vals_2366_);
lean_dec_ref(v_keys_2365_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2372_, lean_object* v_x_2373_, lean_object* v_x_2374_, lean_object* v_x_2375_, lean_object* v_x_2376_){
_start:
{
lean_object* v___x_2377_; 
v___x_2377_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_x_2373_, v_x_2374_, v_x_2375_, v_x_2376_);
return v___x_2377_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0(void){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = l_instMonadEIO(lean_box(0));
return v___x_2378_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__1(void){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__0, &l_Lean_Meta_Sym_instInhabitedSymM___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0);
v___x_2380_ = l_StateRefT_x27_instMonad___redArg(v___x_2379_);
return v___x_2380_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__6(void){
_start:
{
lean_object* v___x_2385_; lean_object* v___f_2386_; 
v___x_2385_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_2386_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2386_, 0, v___x_2385_);
return v___f_2386_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__7(void){
_start:
{
lean_object* v___x_2387_; lean_object* v___f_2388_; 
v___x_2387_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_2388_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2388_, 0, v___x_2387_);
return v___f_2388_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8(void){
_start:
{
lean_object* v___f_2389_; lean_object* v___f_2390_; lean_object* v___x_2391_; 
v___f_2389_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__7, &l_Lean_Meta_Sym_instInhabitedSymM___closed__7_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__7);
v___f_2390_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__6, &l_Lean_Meta_Sym_instInhabitedSymM___closed__6_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__6);
v___x_2391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___f_2390_);
lean_ctor_set(v___x_2391_, 1, v___f_2389_);
return v___x_2391_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__9(void){
_start:
{
lean_object* v___x_2392_; lean_object* v___f_2393_; 
v___x_2392_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__8, &l_Lean_Meta_Sym_instInhabitedSymM___closed__8_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8);
v___f_2393_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2393_, 0, v___x_2392_);
return v___f_2393_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__10(void){
_start:
{
lean_object* v___x_2394_; lean_object* v___f_2395_; 
v___x_2394_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__8, &l_Lean_Meta_Sym_instInhabitedSymM___closed__8_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8);
v___f_2395_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2395_, 0, v___x_2394_);
return v___f_2395_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__11(void){
_start:
{
lean_object* v___f_2396_; lean_object* v___f_2397_; lean_object* v___x_2398_; 
v___f_2396_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__10, &l_Lean_Meta_Sym_instInhabitedSymM___closed__10_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__10);
v___f_2397_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__9, &l_Lean_Meta_Sym_instInhabitedSymM___closed__9_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__9);
v___x_2398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___f_2397_);
lean_ctor_set(v___x_2398_, 1, v___f_2396_);
return v___x_2398_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__12(void){
_start:
{
lean_object* v___x_2399_; lean_object* v___f_2400_; 
v___x_2399_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__11, &l_Lean_Meta_Sym_instInhabitedSymM___closed__11_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__11);
v___f_2400_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2400_, 0, v___x_2399_);
return v___f_2400_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__13(void){
_start:
{
lean_object* v___x_2401_; lean_object* v___f_2402_; 
v___x_2401_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__11, &l_Lean_Meta_Sym_instInhabitedSymM___closed__11_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__11);
v___f_2402_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2402_, 0, v___x_2401_);
return v___f_2402_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__14(void){
_start:
{
lean_object* v___f_2403_; lean_object* v___f_2404_; lean_object* v___x_2405_; 
v___f_2403_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__13, &l_Lean_Meta_Sym_instInhabitedSymM___closed__13_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__13);
v___f_2404_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__12, &l_Lean_Meta_Sym_instInhabitedSymM___closed__12_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__12);
v___x_2405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___f_2404_);
lean_ctor_set(v___x_2405_, 1, v___f_2403_);
return v___x_2405_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__15(void){
_start:
{
lean_object* v___x_2406_; lean_object* v___f_2407_; 
v___x_2406_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__14, &l_Lean_Meta_Sym_instInhabitedSymM___closed__14_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__14);
v___f_2407_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2407_, 0, v___x_2406_);
return v___f_2407_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__16(void){
_start:
{
lean_object* v___x_2408_; lean_object* v___f_2409_; 
v___x_2408_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__14, &l_Lean_Meta_Sym_instInhabitedSymM___closed__14_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__14);
v___f_2409_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2409_, 0, v___x_2408_);
return v___f_2409_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__17(void){
_start:
{
lean_object* v___f_2410_; lean_object* v___f_2411_; lean_object* v___x_2412_; 
v___f_2410_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__16, &l_Lean_Meta_Sym_instInhabitedSymM___closed__16_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__16);
v___f_2411_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__15, &l_Lean_Meta_Sym_instInhabitedSymM___closed__15_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__15);
v___x_2412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___f_2411_);
lean_ctor_set(v___x_2412_, 1, v___f_2410_);
return v___x_2412_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__22(void){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2417_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2418_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__21));
v___x_2419_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__20));
v___x_2420_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2419_, v___x_2418_, v___x_2417_);
return v___x_2420_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__23(void){
_start:
{
lean_object* v___x_2421_; lean_object* v___f_2422_; lean_object* v___f_2423_; lean_object* v___x_2424_; 
v___x_2421_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__22, &l_Lean_Meta_Sym_instInhabitedSymM___closed__22_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__22);
v___f_2422_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__19));
v___f_2423_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__18));
v___x_2424_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2423_, v___f_2422_, v___x_2421_);
return v___x_2424_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__24(void){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2425_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__23, &l_Lean_Meta_Sym_instInhabitedSymM___closed__23_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__23);
v___x_2426_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__21));
v___x_2427_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__20));
v___x_2428_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2427_, v___x_2426_, v___x_2425_);
return v___x_2428_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__25(void){
_start:
{
lean_object* v___x_2429_; lean_object* v___f_2430_; lean_object* v___f_2431_; lean_object* v___x_2432_; 
v___x_2429_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__24, &l_Lean_Meta_Sym_instInhabitedSymM___closed__24_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__24);
v___f_2430_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__19));
v___f_2431_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__18));
v___x_2432_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2431_, v___f_2430_, v___x_2429_);
return v___x_2432_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__26(void){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___f_2435_; 
v___x_2433_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__21));
v___x_2434_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2435_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2435_, 0, v___x_2434_);
lean_closure_set(v___f_2435_, 1, v___x_2433_);
return v___f_2435_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__27(void){
_start:
{
lean_object* v___f_2436_; lean_object* v___f_2437_; lean_object* v___f_2438_; 
v___f_2436_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__19));
v___f_2437_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__26, &l_Lean_Meta_Sym_instInhabitedSymM___closed__26_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__26);
v___f_2438_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2438_, 0, v___f_2437_);
lean_closure_set(v___f_2438_, 1, v___f_2436_);
return v___f_2438_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__29(void){
_start:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2440_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__28));
v___x_2441_ = l_Lean_stringToMessageData(v___x_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object* v_00_u03b1_2442_){
_start:
{
lean_object* v___x_2443_; lean_object* v_toApplicative_2444_; lean_object* v_toFunctor_2445_; lean_object* v_toSeq_2446_; lean_object* v_toSeqLeft_2447_; lean_object* v_toSeqRight_2448_; lean_object* v___f_2449_; lean_object* v___f_2450_; lean_object* v___f_2451_; lean_object* v___f_2452_; lean_object* v___x_2453_; lean_object* v___f_2454_; lean_object* v___f_2455_; lean_object* v___f_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v_toApplicative_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2497_; 
v___x_2443_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__1, &l_Lean_Meta_Sym_instInhabitedSymM___closed__1_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__1);
v_toApplicative_2444_ = lean_ctor_get(v___x_2443_, 0);
v_toFunctor_2445_ = lean_ctor_get(v_toApplicative_2444_, 0);
v_toSeq_2446_ = lean_ctor_get(v_toApplicative_2444_, 2);
v_toSeqLeft_2447_ = lean_ctor_get(v_toApplicative_2444_, 3);
v_toSeqRight_2448_ = lean_ctor_get(v_toApplicative_2444_, 4);
v___f_2449_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__2));
v___f_2450_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__3));
lean_inc_ref_n(v_toFunctor_2445_, 2);
v___f_2451_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2451_, 0, v_toFunctor_2445_);
v___f_2452_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2452_, 0, v_toFunctor_2445_);
v___x_2453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___f_2451_);
lean_ctor_set(v___x_2453_, 1, v___f_2452_);
lean_inc(v_toSeqRight_2448_);
v___f_2454_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2454_, 0, v_toSeqRight_2448_);
lean_inc(v_toSeqLeft_2447_);
v___f_2455_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2455_, 0, v_toSeqLeft_2447_);
lean_inc(v_toSeq_2446_);
v___f_2456_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2456_, 0, v_toSeq_2446_);
v___x_2457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2453_);
lean_ctor_set(v___x_2457_, 1, v___f_2449_);
lean_ctor_set(v___x_2457_, 2, v___f_2456_);
lean_ctor_set(v___x_2457_, 3, v___f_2455_);
lean_ctor_set(v___x_2457_, 4, v___f_2454_);
v___x_2458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
lean_ctor_set(v___x_2458_, 1, v___f_2450_);
v___x_2459_ = l_StateRefT_x27_instMonad___redArg(v___x_2458_);
v_toApplicative_2460_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2497_ == 0)
{
lean_object* v_unused_2498_; 
v_unused_2498_ = lean_ctor_get(v___x_2459_, 1);
lean_dec(v_unused_2498_);
v___x_2462_ = v___x_2459_;
v_isShared_2463_ = v_isSharedCheck_2497_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_toApplicative_2460_);
lean_dec(v___x_2459_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2497_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v_toFunctor_2464_; lean_object* v_toSeq_2465_; lean_object* v_toSeqLeft_2466_; lean_object* v_toSeqRight_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2495_; 
v_toFunctor_2464_ = lean_ctor_get(v_toApplicative_2460_, 0);
v_toSeq_2465_ = lean_ctor_get(v_toApplicative_2460_, 2);
v_toSeqLeft_2466_ = lean_ctor_get(v_toApplicative_2460_, 3);
v_toSeqRight_2467_ = lean_ctor_get(v_toApplicative_2460_, 4);
v_isSharedCheck_2495_ = !lean_is_exclusive(v_toApplicative_2460_);
if (v_isSharedCheck_2495_ == 0)
{
lean_object* v_unused_2496_; 
v_unused_2496_ = lean_ctor_get(v_toApplicative_2460_, 1);
lean_dec(v_unused_2496_);
v___x_2469_ = v_toApplicative_2460_;
v_isShared_2470_ = v_isSharedCheck_2495_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_toSeqRight_2467_);
lean_inc(v_toSeqLeft_2466_);
lean_inc(v_toSeq_2465_);
lean_inc(v_toFunctor_2464_);
lean_dec(v_toApplicative_2460_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2495_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___f_2471_; lean_object* v___f_2472_; lean_object* v___f_2473_; lean_object* v___f_2474_; lean_object* v___x_2475_; lean_object* v___f_2476_; lean_object* v___f_2477_; lean_object* v___f_2478_; lean_object* v___x_2480_; 
v___f_2471_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__4));
v___f_2472_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__5));
lean_inc_ref(v_toFunctor_2464_);
v___f_2473_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2473_, 0, v_toFunctor_2464_);
v___f_2474_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2474_, 0, v_toFunctor_2464_);
v___x_2475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2475_, 0, v___f_2473_);
lean_ctor_set(v___x_2475_, 1, v___f_2474_);
v___f_2476_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2476_, 0, v_toSeqRight_2467_);
v___f_2477_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2477_, 0, v_toSeqLeft_2466_);
v___f_2478_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2478_, 0, v_toSeq_2465_);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 4, v___f_2476_);
lean_ctor_set(v___x_2469_, 3, v___f_2477_);
lean_ctor_set(v___x_2469_, 2, v___f_2478_);
lean_ctor_set(v___x_2469_, 1, v___f_2471_);
lean_ctor_set(v___x_2469_, 0, v___x_2475_);
v___x_2480_ = v___x_2469_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v___f_2471_);
lean_ctor_set(v_reuseFailAlloc_2494_, 2, v___f_2478_);
lean_ctor_set(v_reuseFailAlloc_2494_, 3, v___f_2477_);
lean_ctor_set(v_reuseFailAlloc_2494_, 4, v___f_2476_);
v___x_2480_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
lean_object* v___x_2482_; 
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 1, v___f_2472_);
lean_ctor_set(v___x_2462_, 0, v___x_2480_);
v___x_2482_ = v___x_2462_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2480_);
lean_ctor_set(v_reuseFailAlloc_2493_, 1, v___f_2472_);
v___x_2482_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v_toMonadRef_2487_; lean_object* v___f_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2483_ = l_StateRefT_x27_instMonad___redArg(v___x_2482_);
v___x_2484_ = l_ReaderT_instMonad___redArg(v___x_2483_);
v___x_2485_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__17, &l_Lean_Meta_Sym_instInhabitedSymM___closed__17_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__17);
v___x_2486_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__25, &l_Lean_Meta_Sym_instInhabitedSymM___closed__25_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__25);
v_toMonadRef_2487_ = lean_ctor_get(v___x_2486_, 0);
v___f_2488_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__27, &l_Lean_Meta_Sym_instInhabitedSymM___closed__27_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__27);
lean_inc_ref(v___x_2484_);
v___x_2489_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_2488_, v___x_2484_);
lean_inc_ref(v_toMonadRef_2487_);
v___x_2490_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2485_);
lean_ctor_set(v___x_2490_, 1, v_toMonadRef_2487_);
lean_ctor_set(v___x_2490_, 2, v___x_2489_);
v___x_2491_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__29, &l_Lean_Meta_Sym_instInhabitedSymM___closed__29_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__29);
v___x_2492_ = l_Lean_throwError___redArg(v___x_2484_, v___x_2490_, v___x_2491_);
return v___x_2492_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(lean_object* v_ext_2499_, lean_object* v_extensions_2500_){
_start:
{
lean_object* v_id_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v_id_2502_ = lean_ctor_get(v_ext_2499_, 0);
v___x_2503_ = l_Lean_Meta_Sym_instInhabitedSymExtensionState;
v___x_2504_ = lean_array_get_borrowed(v___x_2503_, v_extensions_2500_, v_id_2502_);
lean_inc(v___x_2504_);
v___x_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2504_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg___boxed(lean_object* v_ext_2506_, lean_object* v_extensions_2507_, lean_object* v_a_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_2506_, v_extensions_2507_);
lean_dec_ref(v_extensions_2507_);
lean_dec_ref(v_ext_2506_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(lean_object* v_00_u03c3_2510_, lean_object* v_ext_2511_, lean_object* v_extensions_2512_){
_start:
{
lean_object* v___x_2514_; 
v___x_2514_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_2511_, v_extensions_2512_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___boxed(lean_object* v_00_u03c3_2515_, lean_object* v_ext_2516_, lean_object* v_extensions_2517_, lean_object* v_a_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(v_00_u03c3_2515_, v_ext_2516_, v_extensions_2517_);
lean_dec_ref(v_extensions_2517_);
lean_dec_ref(v_ext_2516_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg(lean_object* v_ext_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_){
_start:
{
lean_object* v___x_2524_; lean_object* v_extensions_2525_; lean_object* v___x_2526_; 
v___x_2524_ = lean_st_ref_get(v_a_2521_);
v_extensions_2525_ = lean_ctor_get(v___x_2524_, 7);
lean_inc_ref(v_extensions_2525_);
lean_dec(v___x_2524_);
v___x_2526_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_2520_, v_extensions_2525_);
lean_dec_ref(v_extensions_2525_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
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
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2547_; 
v_a_2535_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2537_ = v___x_2526_;
v_isShared_2538_ = v_isSharedCheck_2547_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2526_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2547_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v_ref_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2545_; 
v_ref_2539_ = lean_ctor_get(v_a_2522_, 5);
v___x_2540_ = lean_io_error_to_string(v_a_2535_);
v___x_2541_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
v___x_2542_ = l_Lean_MessageData_ofFormat(v___x_2541_);
lean_inc(v_ref_2539_);
v___x_2543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2543_, 0, v_ref_2539_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 0, v___x_2543_);
v___x_2545_ = v___x_2537_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2543_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg___boxed(lean_object* v_ext_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_2548_, v_a_2549_, v_a_2550_);
lean_dec_ref(v_a_2550_);
lean_dec(v_a_2549_);
lean_dec_ref(v_ext_2548_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState(lean_object* v_00_u03c3_2553_, lean_object* v_ext_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
lean_object* v___x_2562_; 
v___x_2562_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_2554_, v_a_2556_, v_a_2559_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___boxed(lean_object* v_00_u03c3_2563_, lean_object* v_ext_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Lean_Meta_Sym_SymExtension_getState(v_00_u03c3_2563_, v_ext_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
lean_dec(v_a_2570_);
lean_dec_ref(v_a_2569_);
lean_dec(v_a_2568_);
lean_dec_ref(v_a_2567_);
lean_dec(v_a_2566_);
lean_dec_ref(v_a_2565_);
lean_dec_ref(v_ext_2564_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(lean_object* v_ext_2573_, lean_object* v_f_2574_, lean_object* v_a_2575_){
_start:
{
lean_object* v___x_2577_; lean_object* v_share_2578_; lean_object* v_maxFVar_2579_; lean_object* v_proofInstInfo_2580_; lean_object* v_inferType_2581_; lean_object* v_getLevel_2582_; lean_object* v_congrInfo_2583_; lean_object* v_defEqI_2584_; lean_object* v_extensions_2585_; lean_object* v_issues_2586_; lean_object* v_canon_2587_; uint8_t v_debug_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2607_; 
v___x_2577_ = lean_st_ref_take(v_a_2575_);
v_share_2578_ = lean_ctor_get(v___x_2577_, 0);
v_maxFVar_2579_ = lean_ctor_get(v___x_2577_, 1);
v_proofInstInfo_2580_ = lean_ctor_get(v___x_2577_, 2);
v_inferType_2581_ = lean_ctor_get(v___x_2577_, 3);
v_getLevel_2582_ = lean_ctor_get(v___x_2577_, 4);
v_congrInfo_2583_ = lean_ctor_get(v___x_2577_, 5);
v_defEqI_2584_ = lean_ctor_get(v___x_2577_, 6);
v_extensions_2585_ = lean_ctor_get(v___x_2577_, 7);
v_issues_2586_ = lean_ctor_get(v___x_2577_, 8);
v_canon_2587_ = lean_ctor_get(v___x_2577_, 9);
v_debug_2588_ = lean_ctor_get_uint8(v___x_2577_, sizeof(void*)*10);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2590_ = v___x_2577_;
v_isShared_2591_ = v_isSharedCheck_2607_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_canon_2587_);
lean_inc(v_issues_2586_);
lean_inc(v_extensions_2585_);
lean_inc(v_defEqI_2584_);
lean_inc(v_congrInfo_2583_);
lean_inc(v_getLevel_2582_);
lean_inc(v_inferType_2581_);
lean_inc(v_proofInstInfo_2580_);
lean_inc(v_maxFVar_2579_);
lean_inc(v_share_2578_);
lean_dec(v___x_2577_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2607_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v_id_2592_; lean_object* v___x_2593_; lean_object* v___y_2595_; lean_object* v___x_2601_; uint8_t v___x_2602_; 
v_id_2592_ = lean_ctor_get(v_ext_2573_, 0);
v___x_2593_ = lean_box(0);
v___x_2601_ = lean_array_get_size(v_extensions_2585_);
v___x_2602_ = lean_nat_dec_lt(v_id_2592_, v___x_2601_);
if (v___x_2602_ == 0)
{
lean_dec(v_f_2574_);
v___y_2595_ = v_extensions_2585_;
goto v___jp_2594_;
}
else
{
lean_object* v_v_2603_; lean_object* v_xs_x27_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v_v_2603_ = lean_array_fget(v_extensions_2585_, v_id_2592_);
v_xs_x27_2604_ = lean_array_fset(v_extensions_2585_, v_id_2592_, v___x_2593_);
v___x_2605_ = lean_apply_1(v_f_2574_, v_v_2603_);
v___x_2606_ = lean_array_fset(v_xs_x27_2604_, v_id_2592_, v___x_2605_);
v___y_2595_ = v___x_2606_;
goto v___jp_2594_;
}
v___jp_2594_:
{
lean_object* v___x_2597_; 
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 7, v___y_2595_);
v___x_2597_ = v___x_2590_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_share_2578_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v_maxFVar_2579_);
lean_ctor_set(v_reuseFailAlloc_2600_, 2, v_proofInstInfo_2580_);
lean_ctor_set(v_reuseFailAlloc_2600_, 3, v_inferType_2581_);
lean_ctor_set(v_reuseFailAlloc_2600_, 4, v_getLevel_2582_);
lean_ctor_set(v_reuseFailAlloc_2600_, 5, v_congrInfo_2583_);
lean_ctor_set(v_reuseFailAlloc_2600_, 6, v_defEqI_2584_);
lean_ctor_set(v_reuseFailAlloc_2600_, 7, v___y_2595_);
lean_ctor_set(v_reuseFailAlloc_2600_, 8, v_issues_2586_);
lean_ctor_set(v_reuseFailAlloc_2600_, 9, v_canon_2587_);
lean_ctor_set_uint8(v_reuseFailAlloc_2600_, sizeof(void*)*10, v_debug_2588_);
v___x_2597_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = lean_st_ref_set(v_a_2575_, v___x_2597_);
v___x_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2593_);
return v___x_2599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg___boxed(lean_object* v_ext_2608_, lean_object* v_f_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_2608_, v_f_2609_, v_a_2610_);
lean_dec(v_a_2610_);
lean_dec_ref(v_ext_2608_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(lean_object* v_00_u03c3_2613_, lean_object* v_ext_2614_, lean_object* v_f_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_2614_, v_f_2615_, v_a_2617_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___boxed(lean_object* v_00_u03c3_2624_, lean_object* v_ext_2625_, lean_object* v_f_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(v_00_u03c3_2624_, v_ext_2625_, v_f_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
lean_dec(v_a_2630_);
lean_dec_ref(v_a_2629_);
lean_dec(v_a_2628_);
lean_dec_ref(v_a_2627_);
lean_dec_ref(v_ext_2625_);
return v_res_2634_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareCommon(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CongrTheorems(uint8_t builtin);
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
l_Lean_Meta_Sym_instInhabitedConfig_default = _init_l_Lean_Meta_Sym_instInhabitedConfig_default();
l_Lean_Meta_Sym_instInhabitedConfig = _init_l_Lean_Meta_Sym_instInhabitedConfig();
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
