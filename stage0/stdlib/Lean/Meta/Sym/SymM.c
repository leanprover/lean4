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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_226_);
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
lean_dec_ref(v_t_272_);
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
lean_dec_ref(v___x_409_);
if (lean_obj_tag(v_val_411_) == 1)
{
uint8_t v_v_412_; 
v_v_412_ = lean_ctor_get_uint8(v_val_411_, 0);
lean_dec_ref(v_val_411_);
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
lean_dec_ref(v___x_443_);
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
static size_t _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_940_; size_t v___x_941_; size_t v___x_942_; 
v___x_940_ = ((size_t)5ULL);
v___x_941_ = ((size_t)1ULL);
v___x_942_ = lean_usize_shift_left(v___x_941_, v___x_940_);
return v___x_942_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_943_; size_t v___x_944_; size_t v___x_945_; 
v___x_943_ = ((size_t)1ULL);
v___x_944_ = lean_usize_once(&l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__0);
v___x_945_ = lean_usize_sub(v___x_944_, v___x_943_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg(lean_object* v_x_946_, size_t v_x_947_, lean_object* v_x_948_){
_start:
{
if (lean_obj_tag(v_x_946_) == 0)
{
lean_object* v_es_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_977_; 
v_es_949_ = lean_ctor_get(v_x_946_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v_x_946_);
if (v_isSharedCheck_977_ == 0)
{
v___x_951_ = v_x_946_;
v_isShared_952_ = v_isSharedCheck_977_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_es_949_);
lean_dec(v_x_946_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_977_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_953_; size_t v___x_954_; size_t v___x_955_; size_t v___x_956_; lean_object* v_j_957_; lean_object* v___x_958_; 
v___x_953_ = lean_box(2);
v___x_954_ = ((size_t)5ULL);
v___x_955_ = lean_usize_once(&l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1);
v___x_956_ = lean_usize_land(v_x_947_, v___x_955_);
v_j_957_ = lean_usize_to_nat(v___x_956_);
v___x_958_ = lean_array_get(v___x_953_, v_es_949_, v_j_957_);
lean_dec(v_j_957_);
lean_dec_ref(v_es_949_);
switch(lean_obj_tag(v___x_958_))
{
case 0:
{
lean_object* v_key_959_; lean_object* v_val_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_972_; 
v_key_959_ = lean_ctor_get(v___x_958_, 0);
v_val_960_ = lean_ctor_get(v___x_958_, 1);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_972_ == 0)
{
v___x_962_ = v___x_958_;
v_isShared_963_ = v_isSharedCheck_972_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_val_960_);
lean_inc(v_key_959_);
lean_dec(v___x_958_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_972_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
uint8_t v___x_964_; 
lean_inc(v_key_959_);
v___x_964_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_948_, v_key_959_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; 
lean_del_object(v___x_962_);
lean_dec(v_val_960_);
lean_dec(v_key_959_);
lean_del_object(v___x_951_);
v___x_965_ = lean_box(0);
return v___x_965_;
}
else
{
lean_object* v___x_967_; 
if (v_isShared_963_ == 0)
{
v___x_967_ = v___x_962_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_key_959_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_val_960_);
v___x_967_ = v_reuseFailAlloc_971_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
lean_object* v___x_969_; 
if (v_isShared_952_ == 0)
{
lean_ctor_set_tag(v___x_951_, 1);
lean_ctor_set(v___x_951_, 0, v___x_967_);
v___x_969_ = v___x_951_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
}
case 1:
{
lean_object* v_node_973_; size_t v___x_974_; 
lean_del_object(v___x_951_);
v_node_973_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_node_973_);
lean_dec_ref(v___x_958_);
v___x_974_ = lean_usize_shift_right(v_x_947_, v___x_954_);
v_x_946_ = v_node_973_;
v_x_947_ = v___x_974_;
goto _start;
}
default: 
{
lean_object* v___x_976_; 
lean_del_object(v___x_951_);
lean_dec_ref(v_x_948_);
v___x_976_ = lean_box(0);
return v___x_976_;
}
}
}
}
else
{
lean_object* v_ks_978_; lean_object* v_vs_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v_ks_978_ = lean_ctor_get(v_x_946_, 0);
lean_inc_ref(v_ks_978_);
v_vs_979_ = lean_ctor_get(v_x_946_, 1);
lean_inc_ref(v_vs_979_);
lean_dec_ref(v_x_946_);
v___x_980_ = lean_unsigned_to_nat(0u);
v___x_981_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg(v_ks_978_, v_vs_979_, v___x_980_, v_x_948_);
lean_dec_ref(v_vs_979_);
lean_dec_ref(v_ks_978_);
return v___x_981_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___boxed(lean_object* v_x_982_, lean_object* v_x_983_, lean_object* v_x_984_){
_start:
{
size_t v_x_2093__boxed_985_; lean_object* v_res_986_; 
v_x_2093__boxed_985_ = lean_unbox_usize(v_x_983_);
lean_dec(v_x_983_);
v_res_986_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg(v_x_982_, v_x_2093__boxed_985_, v_x_984_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg(lean_object* v_x_987_, lean_object* v_x_988_){
_start:
{
uint64_t v___x_989_; size_t v___x_990_; lean_object* v___x_991_; 
v___x_989_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_988_);
v___x_990_ = lean_uint64_to_usize(v___x_989_);
v___x_991_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg(v_x_987_, v___x_990_, v_x_988_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object* v_e_992_, lean_object* v_a_993_){
_start:
{
lean_object* v___x_995_; lean_object* v_share_996_; lean_object* v_maxFVar_997_; lean_object* v_proofInstInfo_998_; lean_object* v_inferType_999_; lean_object* v_getLevel_1000_; lean_object* v_congrInfo_1001_; lean_object* v_defEqI_1002_; lean_object* v_extensions_1003_; lean_object* v_issues_1004_; lean_object* v_canon_1005_; uint8_t v_debug_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1048_; 
v___x_995_ = lean_st_ref_take(v_a_993_);
v_share_996_ = lean_ctor_get(v___x_995_, 0);
v_maxFVar_997_ = lean_ctor_get(v___x_995_, 1);
v_proofInstInfo_998_ = lean_ctor_get(v___x_995_, 2);
v_inferType_999_ = lean_ctor_get(v___x_995_, 3);
v_getLevel_1000_ = lean_ctor_get(v___x_995_, 4);
v_congrInfo_1001_ = lean_ctor_get(v___x_995_, 5);
v_defEqI_1002_ = lean_ctor_get(v___x_995_, 6);
v_extensions_1003_ = lean_ctor_get(v___x_995_, 7);
v_issues_1004_ = lean_ctor_get(v___x_995_, 8);
v_canon_1005_ = lean_ctor_get(v___x_995_, 9);
v_debug_1006_ = lean_ctor_get_uint8(v___x_995_, sizeof(void*)*10);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1008_ = v___x_995_;
v_isShared_1009_ = v_isSharedCheck_1048_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_canon_1005_);
lean_inc(v_issues_1004_);
lean_inc(v_extensions_1003_);
lean_inc(v_defEqI_1002_);
lean_inc(v_congrInfo_1001_);
lean_inc(v_getLevel_1000_);
lean_inc(v_inferType_999_);
lean_inc(v_proofInstInfo_998_);
lean_inc(v_maxFVar_997_);
lean_inc(v_share_996_);
lean_dec(v___x_995_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1048_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1010_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__0, &l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1010_);
v___x_1012_ = v___x_1008_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_maxFVar_997_);
lean_ctor_set(v_reuseFailAlloc_1047_, 2, v_proofInstInfo_998_);
lean_ctor_set(v_reuseFailAlloc_1047_, 3, v_inferType_999_);
lean_ctor_set(v_reuseFailAlloc_1047_, 4, v_getLevel_1000_);
lean_ctor_set(v_reuseFailAlloc_1047_, 5, v_congrInfo_1001_);
lean_ctor_set(v_reuseFailAlloc_1047_, 6, v_defEqI_1002_);
lean_ctor_set(v_reuseFailAlloc_1047_, 7, v_extensions_1003_);
lean_ctor_set(v_reuseFailAlloc_1047_, 8, v_issues_1004_);
lean_ctor_set(v_reuseFailAlloc_1047_, 9, v_canon_1005_);
lean_ctor_set_uint8(v_reuseFailAlloc_1047_, sizeof(void*)*10, v_debug_1006_);
v___x_1012_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1013_; lean_object* v_fst_1015_; lean_object* v_snd_1016_; lean_object* v___x_1038_; 
v___x_1013_ = lean_st_ref_set(v_a_993_, v___x_1012_);
lean_inc_ref(v_e_992_);
lean_inc_ref(v_share_996_);
v___x_1038_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg(v_share_996_, v_e_992_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v_snd_1042_; lean_object* v_fst_1043_; lean_object* v_set_1044_; 
v___x_1039_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__4, &l_Lean_Meta_Sym_SymM_run___redArg___closed__4_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__4);
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set(v___x_1040_, 1, v_share_996_);
v___x_1041_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_992_, v___x_1040_);
v_snd_1042_ = lean_ctor_get(v___x_1041_, 1);
lean_inc(v_snd_1042_);
v_fst_1043_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_fst_1043_);
lean_dec_ref(v___x_1041_);
v_set_1044_ = lean_ctor_get(v_snd_1042_, 1);
lean_inc_ref(v_set_1044_);
lean_dec(v_snd_1042_);
v_fst_1015_ = v_fst_1043_;
v_snd_1016_ = v_set_1044_;
goto v___jp_1014_;
}
else
{
lean_object* v_val_1045_; lean_object* v_fst_1046_; 
lean_dec_ref(v_e_992_);
v_val_1045_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_val_1045_);
lean_dec_ref(v___x_1038_);
v_fst_1046_ = lean_ctor_get(v_val_1045_, 0);
lean_inc(v_fst_1046_);
lean_dec(v_val_1045_);
v_fst_1015_ = v_fst_1046_;
v_snd_1016_ = v_share_996_;
goto v___jp_1014_;
}
v___jp_1014_:
{
lean_object* v___x_1017_; lean_object* v_maxFVar_1018_; lean_object* v_proofInstInfo_1019_; lean_object* v_inferType_1020_; lean_object* v_getLevel_1021_; lean_object* v_congrInfo_1022_; lean_object* v_defEqI_1023_; lean_object* v_extensions_1024_; lean_object* v_issues_1025_; lean_object* v_canon_1026_; uint8_t v_debug_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1036_; 
v___x_1017_ = lean_st_ref_take(v_a_993_);
v_maxFVar_1018_ = lean_ctor_get(v___x_1017_, 1);
v_proofInstInfo_1019_ = lean_ctor_get(v___x_1017_, 2);
v_inferType_1020_ = lean_ctor_get(v___x_1017_, 3);
v_getLevel_1021_ = lean_ctor_get(v___x_1017_, 4);
v_congrInfo_1022_ = lean_ctor_get(v___x_1017_, 5);
v_defEqI_1023_ = lean_ctor_get(v___x_1017_, 6);
v_extensions_1024_ = lean_ctor_get(v___x_1017_, 7);
v_issues_1025_ = lean_ctor_get(v___x_1017_, 8);
v_canon_1026_ = lean_ctor_get(v___x_1017_, 9);
v_debug_1027_ = lean_ctor_get_uint8(v___x_1017_, sizeof(void*)*10);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1036_ == 0)
{
lean_object* v_unused_1037_; 
v_unused_1037_ = lean_ctor_get(v___x_1017_, 0);
lean_dec(v_unused_1037_);
v___x_1029_ = v___x_1017_;
v_isShared_1030_ = v_isSharedCheck_1036_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_canon_1026_);
lean_inc(v_issues_1025_);
lean_inc(v_extensions_1024_);
lean_inc(v_defEqI_1023_);
lean_inc(v_congrInfo_1022_);
lean_inc(v_getLevel_1021_);
lean_inc(v_inferType_1020_);
lean_inc(v_proofInstInfo_1019_);
lean_inc(v_maxFVar_1018_);
lean_dec(v___x_1017_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1036_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v_snd_1016_);
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_snd_1016_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_maxFVar_1018_);
lean_ctor_set(v_reuseFailAlloc_1035_, 2, v_proofInstInfo_1019_);
lean_ctor_set(v_reuseFailAlloc_1035_, 3, v_inferType_1020_);
lean_ctor_set(v_reuseFailAlloc_1035_, 4, v_getLevel_1021_);
lean_ctor_set(v_reuseFailAlloc_1035_, 5, v_congrInfo_1022_);
lean_ctor_set(v_reuseFailAlloc_1035_, 6, v_defEqI_1023_);
lean_ctor_set(v_reuseFailAlloc_1035_, 7, v_extensions_1024_);
lean_ctor_set(v_reuseFailAlloc_1035_, 8, v_issues_1025_);
lean_ctor_set(v_reuseFailAlloc_1035_, 9, v_canon_1026_);
lean_ctor_set_uint8(v_reuseFailAlloc_1035_, sizeof(void*)*10, v_debug_1027_);
v___x_1032_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = lean_st_ref_set(v_a_993_, v___x_1032_);
v___x_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1034_, 0, v_fst_1015_);
return v___x_1034_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___redArg___boxed(lean_object* v_e_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_Meta_Sym_shareCommon___redArg(v_e_1049_, v_a_1050_);
lean_dec(v_a_1050_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon(lean_object* v_e_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_Meta_Sym_shareCommon___redArg(v_e_1053_, v_a_1055_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommon___boxed(lean_object* v_e_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lean_Meta_Sym_shareCommon(v_e_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0(lean_object* v_00_u03b2_1071_, lean_object* v_x_1072_, lean_object* v_x_1073_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg(v_x_1072_, v_x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0(lean_object* v_00_u03b2_1075_, lean_object* v_x_1076_, size_t v_x_1077_, lean_object* v_x_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg(v_x_1076_, v_x_1077_, v_x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_){
_start:
{
size_t v_x_2275__boxed_1084_; lean_object* v_res_1085_; 
v_x_2275__boxed_1084_ = lean_unbox_usize(v_x_1082_);
lean_dec(v_x_1082_);
v_res_1085_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0(v_00_u03b2_1080_, v_x_1081_, v_x_2275__boxed_1084_, v_x_1083_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1086_, lean_object* v_keys_1087_, lean_object* v_vals_1088_, lean_object* v_heq_1089_, lean_object* v_i_1090_, lean_object* v_k_1091_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg(v_keys_1087_, v_vals_1088_, v_i_1090_, v_k_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1093_, lean_object* v_keys_1094_, lean_object* v_vals_1095_, lean_object* v_heq_1096_, lean_object* v_i_1097_, lean_object* v_k_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1(v_00_u03b2_1093_, v_keys_1094_, v_vals_1095_, v_heq_1096_, v_i_1097_, v_k_1098_);
lean_dec_ref(v_vals_1095_);
lean_dec_ref(v_keys_1094_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object* v_e_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v___x_1103_; lean_object* v_share_1104_; lean_object* v_maxFVar_1105_; lean_object* v_proofInstInfo_1106_; lean_object* v_inferType_1107_; lean_object* v_getLevel_1108_; lean_object* v_congrInfo_1109_; lean_object* v_defEqI_1110_; lean_object* v_extensions_1111_; lean_object* v_issues_1112_; lean_object* v_canon_1113_; uint8_t v_debug_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1147_; 
v___x_1103_ = lean_st_ref_take(v_a_1101_);
v_share_1104_ = lean_ctor_get(v___x_1103_, 0);
v_maxFVar_1105_ = lean_ctor_get(v___x_1103_, 1);
v_proofInstInfo_1106_ = lean_ctor_get(v___x_1103_, 2);
v_inferType_1107_ = lean_ctor_get(v___x_1103_, 3);
v_getLevel_1108_ = lean_ctor_get(v___x_1103_, 4);
v_congrInfo_1109_ = lean_ctor_get(v___x_1103_, 5);
v_defEqI_1110_ = lean_ctor_get(v___x_1103_, 6);
v_extensions_1111_ = lean_ctor_get(v___x_1103_, 7);
v_issues_1112_ = lean_ctor_get(v___x_1103_, 8);
v_canon_1113_ = lean_ctor_get(v___x_1103_, 9);
v_debug_1114_ = lean_ctor_get_uint8(v___x_1103_, sizeof(void*)*10);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1116_ = v___x_1103_;
v_isShared_1117_ = v_isSharedCheck_1147_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_canon_1113_);
lean_inc(v_issues_1112_);
lean_inc(v_extensions_1111_);
lean_inc(v_defEqI_1110_);
lean_inc(v_congrInfo_1109_);
lean_inc(v_getLevel_1108_);
lean_inc(v_inferType_1107_);
lean_inc(v_proofInstInfo_1106_);
lean_inc(v_maxFVar_1105_);
lean_inc(v_share_1104_);
lean_dec(v___x_1103_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1147_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1118_; lean_object* v___x_1120_; 
v___x_1118_ = lean_obj_once(&l_Lean_Meta_Sym_SymM_run___redArg___closed__0, &l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once, _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 0, v___x_1118_);
v___x_1120_ = v___x_1116_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_maxFVar_1105_);
lean_ctor_set(v_reuseFailAlloc_1146_, 2, v_proofInstInfo_1106_);
lean_ctor_set(v_reuseFailAlloc_1146_, 3, v_inferType_1107_);
lean_ctor_set(v_reuseFailAlloc_1146_, 4, v_getLevel_1108_);
lean_ctor_set(v_reuseFailAlloc_1146_, 5, v_congrInfo_1109_);
lean_ctor_set(v_reuseFailAlloc_1146_, 6, v_defEqI_1110_);
lean_ctor_set(v_reuseFailAlloc_1146_, 7, v_extensions_1111_);
lean_ctor_set(v_reuseFailAlloc_1146_, 8, v_issues_1112_);
lean_ctor_set(v_reuseFailAlloc_1146_, 9, v_canon_1113_);
lean_ctor_set_uint8(v_reuseFailAlloc_1146_, sizeof(void*)*10, v_debug_1114_);
v___x_1120_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v_fst_1123_; lean_object* v_snd_1124_; lean_object* v___x_1125_; lean_object* v_maxFVar_1126_; lean_object* v_proofInstInfo_1127_; lean_object* v_inferType_1128_; lean_object* v_getLevel_1129_; lean_object* v_congrInfo_1130_; lean_object* v_defEqI_1131_; lean_object* v_extensions_1132_; lean_object* v_issues_1133_; lean_object* v_canon_1134_; uint8_t v_debug_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1144_; 
v___x_1121_ = lean_st_ref_set(v_a_1101_, v___x_1120_);
v___x_1122_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1100_, v_share_1104_);
v_fst_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_fst_1123_);
v_snd_1124_ = lean_ctor_get(v___x_1122_, 1);
lean_inc(v_snd_1124_);
lean_dec_ref(v___x_1122_);
v___x_1125_ = lean_st_ref_take(v_a_1101_);
v_maxFVar_1126_ = lean_ctor_get(v___x_1125_, 1);
v_proofInstInfo_1127_ = lean_ctor_get(v___x_1125_, 2);
v_inferType_1128_ = lean_ctor_get(v___x_1125_, 3);
v_getLevel_1129_ = lean_ctor_get(v___x_1125_, 4);
v_congrInfo_1130_ = lean_ctor_get(v___x_1125_, 5);
v_defEqI_1131_ = lean_ctor_get(v___x_1125_, 6);
v_extensions_1132_ = lean_ctor_get(v___x_1125_, 7);
v_issues_1133_ = lean_ctor_get(v___x_1125_, 8);
v_canon_1134_ = lean_ctor_get(v___x_1125_, 9);
v_debug_1135_ = lean_ctor_get_uint8(v___x_1125_, sizeof(void*)*10);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v___x_1125_, 0);
lean_dec(v_unused_1145_);
v___x_1137_ = v___x_1125_;
v_isShared_1138_ = v_isSharedCheck_1144_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_canon_1134_);
lean_inc(v_issues_1133_);
lean_inc(v_extensions_1132_);
lean_inc(v_defEqI_1131_);
lean_inc(v_congrInfo_1130_);
lean_inc(v_getLevel_1129_);
lean_inc(v_inferType_1128_);
lean_inc(v_proofInstInfo_1127_);
lean_inc(v_maxFVar_1126_);
lean_dec(v___x_1125_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1144_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v_snd_1124_);
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_snd_1124_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_maxFVar_1126_);
lean_ctor_set(v_reuseFailAlloc_1143_, 2, v_proofInstInfo_1127_);
lean_ctor_set(v_reuseFailAlloc_1143_, 3, v_inferType_1128_);
lean_ctor_set(v_reuseFailAlloc_1143_, 4, v_getLevel_1129_);
lean_ctor_set(v_reuseFailAlloc_1143_, 5, v_congrInfo_1130_);
lean_ctor_set(v_reuseFailAlloc_1143_, 6, v_defEqI_1131_);
lean_ctor_set(v_reuseFailAlloc_1143_, 7, v_extensions_1132_);
lean_ctor_set(v_reuseFailAlloc_1143_, 8, v_issues_1133_);
lean_ctor_set(v_reuseFailAlloc_1143_, 9, v_canon_1134_);
lean_ctor_set_uint8(v_reuseFailAlloc_1143_, sizeof(void*)*10, v_debug_1135_);
v___x_1140_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = lean_st_ref_set(v_a_1101_, v___x_1140_);
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v_fst_1123_);
return v___x_1142_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg___boxed(lean_object* v_e_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_e_1148_, v_a_1149_);
lean_dec(v_a_1149_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object* v_e_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_e_1152_, v_a_1154_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonInc___boxed(lean_object* v_e_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_Meta_Sym_shareCommonInc(v_e_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___redArg(lean_object* v_e_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_e_1170_, v_a_1171_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___redArg___boxed(lean_object* v_e_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_Meta_Sym_share___redArg(v_e_1174_, v_a_1175_);
lean_dec(v_a_1175_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share(lean_object* v_e_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_e_1178_, v_a_1180_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_share___boxed(lean_object* v_e_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_Meta_Sym_share(v_e_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_);
lean_dec(v_a_1193_);
lean_dec_ref(v_a_1192_);
lean_dec(v_a_1191_);
lean_dec_ref(v_a_1190_);
lean_dec(v_a_1189_);
lean_dec_ref(v_a_1188_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg(lean_object* v_a_1196_){
_start:
{
lean_object* v___x_1198_; uint8_t v_debug_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1198_ = lean_st_ref_get(v_a_1196_);
v_debug_1199_ = lean_ctor_get_uint8(v___x_1198_, sizeof(void*)*10);
lean_dec(v___x_1198_);
v___x_1200_ = lean_box(v_debug_1199_);
v___x_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___redArg___boxed(lean_object* v_a_1202_, lean_object* v_a_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_Meta_Sym_isDebugEnabled___redArg(v_a_1202_);
lean_dec(v_a_1202_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled(lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_){
_start:
{
lean_object* v___x_1212_; uint8_t v_debug_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1212_ = lean_st_ref_get(v_a_1206_);
v_debug_1213_ = lean_ctor_get_uint8(v___x_1212_, sizeof(void*)*10);
lean_dec(v___x_1212_);
v___x_1214_ = lean_box(v_debug_1213_);
v___x_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDebugEnabled___boxed(lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_Meta_Sym_isDebugEnabled(v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object* v_a_1224_){
_start:
{
uint8_t v_config_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v_config_1226_ = lean_ctor_get_uint8(v_a_1224_, sizeof(void*)*1);
v___x_1227_ = lean_box(v_config_1226_);
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___redArg___boxed(lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1229_);
lean_dec_ref(v_a_1229_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig(lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1232_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getConfig___boxed(lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_Meta_Sym_getConfig(v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
lean_dec(v_a_1245_);
lean_dec_ref(v_a_1244_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Sym_reportIssue_spec__0(lean_object* v_msgData_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v___x_1254_; lean_object* v_env_1255_; lean_object* v___x_1256_; lean_object* v_mctx_1257_; lean_object* v_lctx_1258_; lean_object* v_options_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1254_ = lean_st_ref_get(v___y_1252_);
v_env_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc_ref(v_env_1255_);
lean_dec(v___x_1254_);
v___x_1256_ = lean_st_ref_get(v___y_1250_);
v_mctx_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc_ref(v_mctx_1257_);
lean_dec(v___x_1256_);
v_lctx_1258_ = lean_ctor_get(v___y_1249_, 2);
v_options_1259_ = lean_ctor_get(v___y_1251_, 2);
lean_inc_ref(v_options_1259_);
lean_inc_ref(v_lctx_1258_);
v___x_1260_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1260_, 0, v_env_1255_);
lean_ctor_set(v___x_1260_, 1, v_mctx_1257_);
lean_ctor_set(v___x_1260_, 2, v_lctx_1258_);
lean_ctor_set(v___x_1260_, 3, v_options_1259_);
v___x_1261_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
lean_ctor_set(v___x_1261_, 1, v_msgData_1248_);
v___x_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Sym_reportIssue_spec__0___boxed(lean_object* v_msgData_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Sym_reportIssue_spec__0(v_msgData_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
return v_res_1269_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1270_; double v___x_1271_; 
v___x_1270_ = lean_unsigned_to_nat(0u);
v___x_1271_ = lean_float_of_nat(v___x_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg(lean_object* v_cls_1275_, lean_object* v_msg_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_ref_1282_; lean_object* v___x_1283_; lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1328_; 
v_ref_1282_ = lean_ctor_get(v___y_1279_, 5);
v___x_1283_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Sym_reportIssue_spec__0(v_msg_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1286_ = v___x_1283_;
v_isShared_1287_ = v_isSharedCheck_1328_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1328_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1288_; lean_object* v_traceState_1289_; lean_object* v_env_1290_; lean_object* v_nextMacroScope_1291_; lean_object* v_ngen_1292_; lean_object* v_auxDeclNGen_1293_; lean_object* v_cache_1294_; lean_object* v_messages_1295_; lean_object* v_infoState_1296_; lean_object* v_snapshotTasks_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1327_; 
v___x_1288_ = lean_st_ref_take(v___y_1280_);
v_traceState_1289_ = lean_ctor_get(v___x_1288_, 4);
v_env_1290_ = lean_ctor_get(v___x_1288_, 0);
v_nextMacroScope_1291_ = lean_ctor_get(v___x_1288_, 1);
v_ngen_1292_ = lean_ctor_get(v___x_1288_, 2);
v_auxDeclNGen_1293_ = lean_ctor_get(v___x_1288_, 3);
v_cache_1294_ = lean_ctor_get(v___x_1288_, 5);
v_messages_1295_ = lean_ctor_get(v___x_1288_, 6);
v_infoState_1296_ = lean_ctor_get(v___x_1288_, 7);
v_snapshotTasks_1297_ = lean_ctor_get(v___x_1288_, 8);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1299_ = v___x_1288_;
v_isShared_1300_ = v_isSharedCheck_1327_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_snapshotTasks_1297_);
lean_inc(v_infoState_1296_);
lean_inc(v_messages_1295_);
lean_inc(v_cache_1294_);
lean_inc(v_traceState_1289_);
lean_inc(v_auxDeclNGen_1293_);
lean_inc(v_ngen_1292_);
lean_inc(v_nextMacroScope_1291_);
lean_inc(v_env_1290_);
lean_dec(v___x_1288_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1327_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
uint64_t v_tid_1301_; lean_object* v_traces_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1326_; 
v_tid_1301_ = lean_ctor_get_uint64(v_traceState_1289_, sizeof(void*)*1);
v_traces_1302_ = lean_ctor_get(v_traceState_1289_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_traceState_1289_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1304_ = v_traceState_1289_;
v_isShared_1305_ = v_isSharedCheck_1326_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_traces_1302_);
lean_dec(v_traceState_1289_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1326_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1306_; double v___x_1307_; uint8_t v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1306_ = lean_box(0);
v___x_1307_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0);
v___x_1308_ = 0;
v___x_1309_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__1));
v___x_1310_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1310_, 0, v_cls_1275_);
lean_ctor_set(v___x_1310_, 1, v___x_1306_);
lean_ctor_set(v___x_1310_, 2, v___x_1309_);
lean_ctor_set_float(v___x_1310_, sizeof(void*)*3, v___x_1307_);
lean_ctor_set_float(v___x_1310_, sizeof(void*)*3 + 8, v___x_1307_);
lean_ctor_set_uint8(v___x_1310_, sizeof(void*)*3 + 16, v___x_1308_);
v___x_1311_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__2));
v___x_1312_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1310_);
lean_ctor_set(v___x_1312_, 1, v_a_1284_);
lean_ctor_set(v___x_1312_, 2, v___x_1311_);
lean_inc(v_ref_1282_);
v___x_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1313_, 0, v_ref_1282_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = l_Lean_PersistentArray_push___redArg(v_traces_1302_, v___x_1313_);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v___x_1314_);
v___x_1316_ = v___x_1304_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1314_);
lean_ctor_set_uint64(v_reuseFailAlloc_1325_, sizeof(void*)*1, v_tid_1301_);
v___x_1316_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1318_; 
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 4, v___x_1316_);
v___x_1318_ = v___x_1299_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_env_1290_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_nextMacroScope_1291_);
lean_ctor_set(v_reuseFailAlloc_1324_, 2, v_ngen_1292_);
lean_ctor_set(v_reuseFailAlloc_1324_, 3, v_auxDeclNGen_1293_);
lean_ctor_set(v_reuseFailAlloc_1324_, 4, v___x_1316_);
lean_ctor_set(v_reuseFailAlloc_1324_, 5, v_cache_1294_);
lean_ctor_set(v_reuseFailAlloc_1324_, 6, v_messages_1295_);
lean_ctor_set(v_reuseFailAlloc_1324_, 7, v_infoState_1296_);
lean_ctor_set(v_reuseFailAlloc_1324_, 8, v_snapshotTasks_1297_);
v___x_1318_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1319_ = lean_st_ref_set(v___y_1280_, v___x_1318_);
v___x_1320_ = lean_box(0);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 0, v___x_1320_);
v___x_1322_ = v___x_1286_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___boxed(lean_object* v_cls_1329_, lean_object* v_msg_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg(v_cls_1329_, v_msg_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
return v_res_1336_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_reportIssue___closed__2(void){
_start:
{
lean_object* v___x_1340_; uint8_t v___x_1341_; double v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1340_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__1));
v___x_1341_ = 1;
v___x_1342_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0);
v___x_1343_ = lean_box(0);
v___x_1344_ = ((lean_object*)(l_Lean_Meta_Sym_reportIssue___closed__1));
v___x_1345_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
lean_ctor_set(v___x_1345_, 1, v___x_1343_);
lean_ctor_set(v___x_1345_, 2, v___x_1340_);
lean_ctor_set_float(v___x_1345_, sizeof(void*)*3, v___x_1342_);
lean_ctor_set_float(v___x_1345_, sizeof(void*)*3 + 8, v___x_1342_);
lean_ctor_set_uint8(v___x_1345_, sizeof(void*)*3 + 16, v___x_1341_);
return v___x_1345_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_reportIssue___closed__5(void){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1349_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_1350_ = ((lean_object*)(l_Lean_Meta_Sym_reportIssue___closed__4));
v___x_1351_ = l_Lean_Name_append(v___x_1350_, v___x_1349_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue(lean_object* v_msg_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_){
_start:
{
lean_object* v___x_1363_; lean_object* v_a_1364_; lean_object* v___x_1365_; lean_object* v_share_1366_; lean_object* v_maxFVar_1367_; lean_object* v_proofInstInfo_1368_; lean_object* v_inferType_1369_; lean_object* v_getLevel_1370_; lean_object* v_congrInfo_1371_; lean_object* v_defEqI_1372_; lean_object* v_extensions_1373_; lean_object* v_issues_1374_; lean_object* v_canon_1375_; uint8_t v_debug_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1395_; 
v___x_1363_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Sym_reportIssue_spec__0(v_msg_1352_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref(v___x_1363_);
v___x_1365_ = lean_st_ref_take(v_a_1354_);
v_share_1366_ = lean_ctor_get(v___x_1365_, 0);
v_maxFVar_1367_ = lean_ctor_get(v___x_1365_, 1);
v_proofInstInfo_1368_ = lean_ctor_get(v___x_1365_, 2);
v_inferType_1369_ = lean_ctor_get(v___x_1365_, 3);
v_getLevel_1370_ = lean_ctor_get(v___x_1365_, 4);
v_congrInfo_1371_ = lean_ctor_get(v___x_1365_, 5);
v_defEqI_1372_ = lean_ctor_get(v___x_1365_, 6);
v_extensions_1373_ = lean_ctor_get(v___x_1365_, 7);
v_issues_1374_ = lean_ctor_get(v___x_1365_, 8);
v_canon_1375_ = lean_ctor_get(v___x_1365_, 9);
v_debug_1376_ = lean_ctor_get_uint8(v___x_1365_, sizeof(void*)*10);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1378_ = v___x_1365_;
v_isShared_1379_ = v_isSharedCheck_1395_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_canon_1375_);
lean_inc(v_issues_1374_);
lean_inc(v_extensions_1373_);
lean_inc(v_defEqI_1372_);
lean_inc(v_congrInfo_1371_);
lean_inc(v_getLevel_1370_);
lean_inc(v_inferType_1369_);
lean_inc(v_proofInstInfo_1368_);
lean_inc(v_maxFVar_1367_);
lean_inc(v_share_1366_);
lean_dec(v___x_1365_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1395_;
goto v_resetjp_1377_;
}
v___jp_1360_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = lean_box(0);
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
return v___x_1362_;
}
v_resetjp_1377_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1380_ = lean_obj_once(&l_Lean_Meta_Sym_reportIssue___closed__2, &l_Lean_Meta_Sym_reportIssue___closed__2_once, _init_l_Lean_Meta_Sym_reportIssue___closed__2);
v___x_1381_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__2));
lean_inc(v_a_1364_);
v___x_1382_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1380_);
lean_ctor_set(v___x_1382_, 1, v_a_1364_);
lean_ctor_set(v___x_1382_, 2, v___x_1381_);
v___x_1383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
lean_ctor_set(v___x_1383_, 1, v_issues_1374_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 8, v___x_1383_);
v___x_1385_ = v___x_1378_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_share_1366_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_maxFVar_1367_);
lean_ctor_set(v_reuseFailAlloc_1394_, 2, v_proofInstInfo_1368_);
lean_ctor_set(v_reuseFailAlloc_1394_, 3, v_inferType_1369_);
lean_ctor_set(v_reuseFailAlloc_1394_, 4, v_getLevel_1370_);
lean_ctor_set(v_reuseFailAlloc_1394_, 5, v_congrInfo_1371_);
lean_ctor_set(v_reuseFailAlloc_1394_, 6, v_defEqI_1372_);
lean_ctor_set(v_reuseFailAlloc_1394_, 7, v_extensions_1373_);
lean_ctor_set(v_reuseFailAlloc_1394_, 8, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1394_, 9, v_canon_1375_);
lean_ctor_set_uint8(v_reuseFailAlloc_1394_, sizeof(void*)*10, v_debug_1376_);
v___x_1385_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
lean_object* v___x_1386_; lean_object* v_options_1387_; uint8_t v_hasTrace_1388_; 
v___x_1386_ = lean_st_ref_set(v_a_1354_, v___x_1385_);
v_options_1387_ = lean_ctor_get(v_a_1357_, 2);
v_hasTrace_1388_ = lean_ctor_get_uint8(v_options_1387_, sizeof(void*)*1);
if (v_hasTrace_1388_ == 0)
{
lean_dec(v_a_1364_);
goto v___jp_1360_;
}
else
{
lean_object* v_inheritedTraceOptions_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v_inheritedTraceOptions_1389_ = lean_ctor_get(v_a_1357_, 13);
v___x_1390_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_));
v___x_1391_ = lean_obj_once(&l_Lean_Meta_Sym_reportIssue___closed__5, &l_Lean_Meta_Sym_reportIssue___closed__5_once, _init_l_Lean_Meta_Sym_reportIssue___closed__5);
v___x_1392_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1389_, v_options_1387_, v___x_1391_);
if (v___x_1392_ == 0)
{
lean_dec(v_a_1364_);
goto v___jp_1360_;
}
else
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg(v___x_1390_, v_a_1364_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
return v___x_1393_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssue___boxed(lean_object* v_msg_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_Meta_Sym_reportIssue(v_msg_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1(lean_object* v_cls_1405_, lean_object* v_msg_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg(v_cls_1405_, v_msg_1406_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___boxed(lean_object* v_cls_1415_, lean_object* v_msg_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1(v_cls_1415_, v_msg_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose(lean_object* v_msg_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v___x_1433_; lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1444_; 
v___x_1433_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1426_);
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1444_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1444_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
uint8_t v___x_1438_; 
v___x_1438_ = lean_unbox(v_a_1434_);
lean_dec(v_a_1434_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
lean_dec_ref(v_msg_1425_);
v___x_1439_ = lean_box(0);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1439_);
v___x_1441_ = v___x_1436_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1439_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
else
{
lean_object* v___x_1443_; 
lean_del_object(v___x_1436_);
v___x_1443_ = l_Lean_Meta_Sym_reportIssue(v_msg_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_);
return v___x_1443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportIssueIfVerbose___boxed(lean_object* v_msg_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Lean_Meta_Sym_reportIssueIfVerbose(v_msg_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_);
lean_dec(v_a_1451_);
lean_dec_ref(v_a_1450_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
return v_res_1453_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7(void){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6));
v___x_1470_ = l_String_toRawSubstring_x27(v___x_1469_);
return v___x_1470_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24(void){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__1));
v___x_1509_ = l_String_toRawSubstring_x27(v___x_1508_);
return v___x_1509_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29));
v___x_1522_ = l_String_toRawSubstring_x27(v___x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(lean_object* v_s_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v_msg_1549_; lean_object* v_quotContext_1550_; lean_object* v_currMacroScope_1551_; lean_object* v_ref_1552_; lean_object* v___y_1553_; lean_object* v___x_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
lean_inc(v_s_1545_);
v___x_1568_ = l_Lean_Syntax_getKind(v_s_1545_);
v___x_1569_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16));
v___x_1570_ = lean_name_eq(v___x_1568_, v___x_1569_);
lean_dec(v___x_1568_);
if (v___x_1570_ == 0)
{
lean_object* v_quotContext_1571_; lean_object* v_currMacroScope_1572_; lean_object* v_ref_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v_quotContext_1571_ = lean_ctor_get(v_a_1546_, 1);
v_currMacroScope_1572_ = lean_ctor_get(v_a_1546_, 2);
v_ref_1573_ = lean_ctor_get(v_a_1546_, 5);
v___x_1574_ = l_Lean_SourceInfo_fromRef(v_ref_1573_, v___x_1570_);
v___x_1575_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18));
v___x_1576_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20));
v___x_1577_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21));
lean_inc_n(v___x_1574_, 8);
v___x_1578_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1574_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23));
v___x_1580_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
v___x_1581_ = lean_box(0);
lean_inc_n(v_currMacroScope_1572_, 3);
lean_inc_n(v_quotContext_1571_, 3);
v___x_1582_ = l_Lean_addMacroScope(v_quotContext_1571_, v___x_1581_, v_currMacroScope_1572_);
v___x_1583_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27));
v___x_1584_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1574_);
lean_ctor_set(v___x_1584_, 1, v___x_1580_);
lean_ctor_set(v___x_1584_, 2, v___x_1582_);
lean_ctor_set(v___x_1584_, 3, v___x_1583_);
v___x_1585_ = l_Lean_Syntax_node1(v___x_1574_, v___x_1579_, v___x_1584_);
v___x_1586_ = l_Lean_Syntax_node2(v___x_1574_, v___x_1576_, v___x_1578_, v___x_1585_);
v___x_1587_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28));
v___x_1588_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1574_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_1590_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
v___x_1591_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31));
v___x_1592_ = l_Lean_addMacroScope(v_quotContext_1571_, v___x_1591_, v_currMacroScope_1572_);
v___x_1593_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36));
v___x_1594_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1574_);
lean_ctor_set(v___x_1594_, 1, v___x_1590_);
lean_ctor_set(v___x_1594_, 2, v___x_1592_);
lean_ctor_set(v___x_1594_, 3, v___x_1593_);
v___x_1595_ = l_Lean_Syntax_node1(v___x_1574_, v___x_1589_, v___x_1594_);
v___x_1596_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37));
v___x_1597_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1574_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = l_Lean_Syntax_node5(v___x_1574_, v___x_1575_, v___x_1586_, v_s_1545_, v___x_1588_, v___x_1595_, v___x_1597_);
v_msg_1549_ = v___x_1598_;
v_quotContext_1550_ = v_quotContext_1571_;
v_currMacroScope_1551_ = v_currMacroScope_1572_;
v_ref_1552_ = v_ref_1573_;
v___y_1553_ = v_a_1547_;
goto v___jp_1548_;
}
else
{
lean_object* v_quotContext_1599_; lean_object* v_currMacroScope_1600_; lean_object* v_ref_1601_; uint8_t v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v_quotContext_1599_ = lean_ctor_get(v_a_1546_, 1);
v_currMacroScope_1600_ = lean_ctor_get(v_a_1546_, 2);
v_ref_1601_ = lean_ctor_get(v_a_1546_, 5);
v___x_1602_ = 0;
v___x_1603_ = l_Lean_SourceInfo_fromRef(v_ref_1601_, v___x_1602_);
v___x_1604_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39));
v___x_1605_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40));
lean_inc(v___x_1603_);
v___x_1606_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1603_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v___x_1607_ = l_Lean_Syntax_node2(v___x_1603_, v___x_1604_, v___x_1606_, v_s_1545_);
lean_inc(v_currMacroScope_1600_);
lean_inc(v_quotContext_1599_);
v_msg_1549_ = v___x_1607_;
v_quotContext_1550_ = v_quotContext_1599_;
v_currMacroScope_1551_ = v_currMacroScope_1600_;
v_ref_1552_ = v_ref_1601_;
v___y_1553_ = v_a_1547_;
goto v___jp_1548_;
}
v___jp_1548_:
{
uint8_t v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1554_ = 0;
v___x_1555_ = l_Lean_SourceInfo_fromRef(v_ref_1552_, v___x_1554_);
v___x_1556_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3));
v___x_1557_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5));
v___x_1558_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7);
v___x_1559_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9));
v___x_1560_ = l_Lean_addMacroScope(v_quotContext_1550_, v___x_1559_, v_currMacroScope_1551_);
v___x_1561_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12));
lean_inc_n(v___x_1555_, 3);
v___x_1562_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1555_);
lean_ctor_set(v___x_1562_, 1, v___x_1558_);
lean_ctor_set(v___x_1562_, 2, v___x_1560_);
lean_ctor_set(v___x_1562_, 3, v___x_1561_);
v___x_1563_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_1564_ = l_Lean_Syntax_node1(v___x_1555_, v___x_1563_, v_msg_1549_);
v___x_1565_ = l_Lean_Syntax_node2(v___x_1555_, v___x_1557_, v___x_1562_, v___x_1564_);
v___x_1566_ = l_Lean_Syntax_node1(v___x_1555_, v___x_1556_, v___x_1565_);
v___x_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
lean_ctor_set(v___x_1567_, 1, v___y_1553_);
return v___x_1567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___boxed(lean_object* v_s_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(v_s_1608_, v_a_1609_, v_a_1610_);
lean_dec_ref(v_a_1609_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(lean_object* v_x_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1655_ = ((lean_object*)(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1));
lean_inc(v_x_1652_);
v___x_1656_ = l_Lean_Syntax_isOfKind(v_x_1652_, v___x_1655_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
lean_dec(v_x_1652_);
v___x_1657_ = lean_box(1);
v___x_1658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
lean_ctor_set(v___x_1658_, 1, v_a_1654_);
return v___x_1658_;
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v_a_1662_; lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
v___x_1659_ = lean_unsigned_to_nat(1u);
v___x_1660_ = l_Lean_Syntax_getArg(v_x_1652_, v___x_1659_);
lean_dec(v_x_1652_);
v___x_1661_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(v___x_1660_, v_a_1653_, v_a_1654_);
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_a_1663_ = lean_ctor_get(v___x_1661_, 1);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1661_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1662_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1___boxed(lean_object* v_x_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(v_x_1671_, v_a_1672_, v_a_1673_);
lean_dec_ref(v_a_1672_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue(lean_object* v_msg_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v___x_1683_; lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1703_; 
v___x_1683_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1676_);
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1686_ = v___x_1683_;
v_isShared_1687_ = v_isSharedCheck_1703_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1683_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1703_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
uint8_t v___x_1688_; 
v___x_1688_ = lean_unbox(v_a_1684_);
lean_dec(v_a_1684_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1691_; 
lean_dec_ref(v_msg_1675_);
v___x_1689_ = lean_box(0);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1689_);
v___x_1691_ = v___x_1686_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
else
{
lean_object* v_options_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; uint8_t v___x_1697_; 
v_options_1693_ = lean_ctor_get(v_a_1680_, 2);
v___x_1694_ = l_Lean_KVMap_instValueBool;
v___x_1695_ = l_Lean_Meta_Sym_sym_debug;
v___x_1696_ = l_Lean_Option_get___redArg(v___x_1694_, v_options_1693_, v___x_1695_);
v___x_1697_ = lean_unbox(v___x_1696_);
lean_dec(v___x_1696_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; lean_object* v___x_1700_; 
lean_dec_ref(v_msg_1675_);
v___x_1698_ = lean_box(0);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1698_);
v___x_1700_ = v___x_1686_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
else
{
lean_object* v___x_1702_; 
lean_del_object(v___x_1686_);
v___x_1702_ = l_Lean_Meta_Sym_reportIssue(v_msg_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
return v___x_1702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reportDbgIssue___boxed(lean_object* v_msg_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_Meta_Sym_reportDbgIssue(v_msg_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
lean_dec(v_a_1708_);
lean_dec_ref(v_a_1707_);
lean_dec(v_a_1706_);
lean_dec_ref(v_a_1705_);
return v_res_1712_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1(void){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0));
v___x_1715_ = l_String_toRawSubstring_x27(v___x_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro(lean_object* v_s_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v_msg_1735_; lean_object* v_quotContext_1736_; lean_object* v_currMacroScope_1737_; lean_object* v_ref_1738_; lean_object* v___y_1739_; lean_object* v___x_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
lean_inc(v_s_1731_);
v___x_1754_ = l_Lean_Syntax_getKind(v_s_1731_);
v___x_1755_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16));
v___x_1756_ = lean_name_eq(v___x_1754_, v___x_1755_);
lean_dec(v___x_1754_);
if (v___x_1756_ == 0)
{
lean_object* v_quotContext_1757_; lean_object* v_currMacroScope_1758_; lean_object* v_ref_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v_quotContext_1757_ = lean_ctor_get(v_a_1732_, 1);
v_currMacroScope_1758_ = lean_ctor_get(v_a_1732_, 2);
v_ref_1759_ = lean_ctor_get(v_a_1732_, 5);
v___x_1760_ = l_Lean_SourceInfo_fromRef(v_ref_1759_, v___x_1756_);
v___x_1761_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18));
v___x_1762_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20));
v___x_1763_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21));
lean_inc_n(v___x_1760_, 8);
v___x_1764_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1760_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
v___x_1765_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23));
v___x_1766_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
v___x_1767_ = lean_box(0);
lean_inc_n(v_currMacroScope_1758_, 3);
lean_inc_n(v_quotContext_1757_, 3);
v___x_1768_ = l_Lean_addMacroScope(v_quotContext_1757_, v___x_1767_, v_currMacroScope_1758_);
v___x_1769_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27));
v___x_1770_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1760_);
lean_ctor_set(v___x_1770_, 1, v___x_1766_);
lean_ctor_set(v___x_1770_, 2, v___x_1768_);
lean_ctor_set(v___x_1770_, 3, v___x_1769_);
v___x_1771_ = l_Lean_Syntax_node1(v___x_1760_, v___x_1765_, v___x_1770_);
v___x_1772_ = l_Lean_Syntax_node2(v___x_1760_, v___x_1762_, v___x_1764_, v___x_1771_);
v___x_1773_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28));
v___x_1774_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1760_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_1776_ = lean_obj_once(&l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30, &l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once, _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
v___x_1777_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31));
v___x_1778_ = l_Lean_addMacroScope(v_quotContext_1757_, v___x_1777_, v_currMacroScope_1758_);
v___x_1779_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36));
v___x_1780_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1760_);
lean_ctor_set(v___x_1780_, 1, v___x_1776_);
lean_ctor_set(v___x_1780_, 2, v___x_1778_);
lean_ctor_set(v___x_1780_, 3, v___x_1779_);
v___x_1781_ = l_Lean_Syntax_node1(v___x_1760_, v___x_1775_, v___x_1780_);
v___x_1782_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37));
v___x_1783_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1760_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
v___x_1784_ = l_Lean_Syntax_node5(v___x_1760_, v___x_1761_, v___x_1772_, v_s_1731_, v___x_1774_, v___x_1781_, v___x_1783_);
v_msg_1735_ = v___x_1784_;
v_quotContext_1736_ = v_quotContext_1757_;
v_currMacroScope_1737_ = v_currMacroScope_1758_;
v_ref_1738_ = v_ref_1759_;
v___y_1739_ = v_a_1733_;
goto v___jp_1734_;
}
else
{
lean_object* v_quotContext_1785_; lean_object* v_currMacroScope_1786_; lean_object* v_ref_1787_; uint8_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v_quotContext_1785_ = lean_ctor_get(v_a_1732_, 1);
v_currMacroScope_1786_ = lean_ctor_get(v_a_1732_, 2);
v_ref_1787_ = lean_ctor_get(v_a_1732_, 5);
v___x_1788_ = 0;
v___x_1789_ = l_Lean_SourceInfo_fromRef(v_ref_1787_, v___x_1788_);
v___x_1790_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39));
v___x_1791_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40));
lean_inc(v___x_1789_);
v___x_1792_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1789_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v___x_1793_ = l_Lean_Syntax_node2(v___x_1789_, v___x_1790_, v___x_1792_, v_s_1731_);
lean_inc(v_currMacroScope_1786_);
lean_inc(v_quotContext_1785_);
v_msg_1735_ = v___x_1793_;
v_quotContext_1736_ = v_quotContext_1785_;
v_currMacroScope_1737_ = v_currMacroScope_1786_;
v_ref_1738_ = v_ref_1787_;
v___y_1739_ = v_a_1733_;
goto v___jp_1734_;
}
v___jp_1734_:
{
uint8_t v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1740_ = 0;
v___x_1741_ = l_Lean_SourceInfo_fromRef(v_ref_1738_, v___x_1740_);
v___x_1742_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3));
v___x_1743_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5));
v___x_1744_ = lean_obj_once(&l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1, &l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1_once, _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1);
v___x_1745_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3));
v___x_1746_ = l_Lean_addMacroScope(v_quotContext_1736_, v___x_1745_, v_currMacroScope_1737_);
v___x_1747_ = ((lean_object*)(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6));
lean_inc_n(v___x_1741_, 3);
v___x_1748_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1741_);
lean_ctor_set(v___x_1748_, 1, v___x_1744_);
lean_ctor_set(v___x_1748_, 2, v___x_1746_);
lean_ctor_set(v___x_1748_, 3, v___x_1747_);
v___x_1749_ = ((lean_object*)(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14));
v___x_1750_ = l_Lean_Syntax_node1(v___x_1741_, v___x_1749_, v_msg_1735_);
v___x_1751_ = l_Lean_Syntax_node2(v___x_1741_, v___x_1743_, v___x_1748_, v___x_1750_);
v___x_1752_ = l_Lean_Syntax_node1(v___x_1741_, v___x_1742_, v___x_1751_);
v___x_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
lean_ctor_set(v___x_1753_, 1, v___y_1739_);
return v___x_1753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_expandReportDbgIssueMacro___boxed(lean_object* v_s_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v_s_1794_, v_a_1795_, v_a_1796_);
lean_dec_ref(v_a_1795_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(lean_object* v_x_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v___x_1819_; uint8_t v___x_1820_; 
v___x_1819_ = ((lean_object*)(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1));
lean_inc(v_x_1816_);
v___x_1820_ = l_Lean_Syntax_isOfKind(v_x_1816_, v___x_1819_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
lean_dec(v_x_1816_);
v___x_1821_ = lean_box(1);
v___x_1822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
lean_ctor_set(v___x_1822_, 1, v_a_1818_);
return v___x_1822_;
}
else
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v_a_1826_; lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
v___x_1823_ = lean_unsigned_to_nat(1u);
v___x_1824_ = l_Lean_Syntax_getArg(v_x_1816_, v___x_1823_);
lean_dec(v_x_1816_);
v___x_1825_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v___x_1824_, v_a_1817_, v_a_1818_);
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
v_a_1827_ = lean_ctor_get(v___x_1825_, 1);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1829_ = v___x_1825_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_inc(v_a_1826_);
lean_dec(v___x_1825_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1826_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1___boxed(lean_object* v_x_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(v_x_1835_, v_a_1836_, v_a_1837_);
lean_dec_ref(v_a_1836_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg(lean_object* v_a_1839_){
_start:
{
lean_object* v___x_1841_; lean_object* v_issues_1842_; lean_object* v___x_1843_; 
v___x_1841_ = lean_st_ref_get(v_a_1839_);
v_issues_1842_ = lean_ctor_get(v___x_1841_, 8);
lean_inc(v_issues_1842_);
lean_dec(v___x_1841_);
v___x_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1843_, 0, v_issues_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___redArg___boxed(lean_object* v_a_1844_, lean_object* v_a_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_1844_);
lean_dec(v_a_1844_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues(lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_1848_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIssues___boxed(lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_Meta_Sym_getIssues(v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_);
lean_dec(v_a_1860_);
lean_dec_ref(v_a_1859_);
lean_dec(v_a_1858_);
lean_dec_ref(v_a_1857_);
lean_dec(v_a_1856_);
lean_dec_ref(v_a_1855_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(lean_object* v_a_1863_, lean_object* v_issues_1864_, lean_object* v_a_x3f_1865_){
_start:
{
lean_object* v___x_1867_; lean_object* v_share_1868_; lean_object* v_maxFVar_1869_; lean_object* v_proofInstInfo_1870_; lean_object* v_inferType_1871_; lean_object* v_getLevel_1872_; lean_object* v_congrInfo_1873_; lean_object* v_defEqI_1874_; lean_object* v_extensions_1875_; lean_object* v_issues_1876_; lean_object* v_canon_1877_; uint8_t v_debug_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1889_; 
v___x_1867_ = lean_st_ref_take(v_a_1863_);
v_share_1868_ = lean_ctor_get(v___x_1867_, 0);
v_maxFVar_1869_ = lean_ctor_get(v___x_1867_, 1);
v_proofInstInfo_1870_ = lean_ctor_get(v___x_1867_, 2);
v_inferType_1871_ = lean_ctor_get(v___x_1867_, 3);
v_getLevel_1872_ = lean_ctor_get(v___x_1867_, 4);
v_congrInfo_1873_ = lean_ctor_get(v___x_1867_, 5);
v_defEqI_1874_ = lean_ctor_get(v___x_1867_, 6);
v_extensions_1875_ = lean_ctor_get(v___x_1867_, 7);
v_issues_1876_ = lean_ctor_get(v___x_1867_, 8);
v_canon_1877_ = lean_ctor_get(v___x_1867_, 9);
v_debug_1878_ = lean_ctor_get_uint8(v___x_1867_, sizeof(void*)*10);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1880_ = v___x_1867_;
v_isShared_1881_ = v_isSharedCheck_1889_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_canon_1877_);
lean_inc(v_issues_1876_);
lean_inc(v_extensions_1875_);
lean_inc(v_defEqI_1874_);
lean_inc(v_congrInfo_1873_);
lean_inc(v_getLevel_1872_);
lean_inc(v_inferType_1871_);
lean_inc(v_proofInstInfo_1870_);
lean_inc(v_maxFVar_1869_);
lean_inc(v_share_1868_);
lean_dec(v___x_1867_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1889_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1884_; 
v___x_1882_ = l_List_appendTR___redArg(v_issues_1876_, v_issues_1864_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 8, v___x_1882_);
v___x_1884_ = v___x_1880_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_share_1868_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_maxFVar_1869_);
lean_ctor_set(v_reuseFailAlloc_1888_, 2, v_proofInstInfo_1870_);
lean_ctor_set(v_reuseFailAlloc_1888_, 3, v_inferType_1871_);
lean_ctor_set(v_reuseFailAlloc_1888_, 4, v_getLevel_1872_);
lean_ctor_set(v_reuseFailAlloc_1888_, 5, v_congrInfo_1873_);
lean_ctor_set(v_reuseFailAlloc_1888_, 6, v_defEqI_1874_);
lean_ctor_set(v_reuseFailAlloc_1888_, 7, v_extensions_1875_);
lean_ctor_set(v_reuseFailAlloc_1888_, 8, v___x_1882_);
lean_ctor_set(v_reuseFailAlloc_1888_, 9, v_canon_1877_);
lean_ctor_set_uint8(v_reuseFailAlloc_1888_, sizeof(void*)*10, v_debug_1878_);
v___x_1884_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1885_ = lean_st_ref_set(v_a_1863_, v___x_1884_);
v___x_1886_ = lean_box(0);
v___x_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
return v___x_1887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0___boxed(lean_object* v_a_1890_, lean_object* v_issues_1891_, lean_object* v_a_x3f_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_1890_, v_issues_1891_, v_a_x3f_1892_);
lean_dec(v_a_x3f_1892_);
lean_dec(v_a_1890_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg(lean_object* v_x_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v_share_1905_; lean_object* v_maxFVar_1906_; lean_object* v_proofInstInfo_1907_; lean_object* v_inferType_1908_; lean_object* v_getLevel_1909_; lean_object* v_congrInfo_1910_; lean_object* v_defEqI_1911_; lean_object* v_extensions_1912_; lean_object* v_canon_1913_; uint8_t v_debug_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1953_; 
v___x_1903_ = lean_st_ref_get(v_a_1897_);
v___x_1904_ = lean_st_ref_take(v_a_1897_);
v_share_1905_ = lean_ctor_get(v___x_1904_, 0);
v_maxFVar_1906_ = lean_ctor_get(v___x_1904_, 1);
v_proofInstInfo_1907_ = lean_ctor_get(v___x_1904_, 2);
v_inferType_1908_ = lean_ctor_get(v___x_1904_, 3);
v_getLevel_1909_ = lean_ctor_get(v___x_1904_, 4);
v_congrInfo_1910_ = lean_ctor_get(v___x_1904_, 5);
v_defEqI_1911_ = lean_ctor_get(v___x_1904_, 6);
v_extensions_1912_ = lean_ctor_get(v___x_1904_, 7);
v_canon_1913_ = lean_ctor_get(v___x_1904_, 9);
v_debug_1914_ = lean_ctor_get_uint8(v___x_1904_, sizeof(void*)*10);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1953_ == 0)
{
lean_object* v_unused_1954_; 
v_unused_1954_ = lean_ctor_get(v___x_1904_, 8);
lean_dec(v_unused_1954_);
v___x_1916_ = v___x_1904_;
v_isShared_1917_ = v_isSharedCheck_1953_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_canon_1913_);
lean_inc(v_extensions_1912_);
lean_inc(v_defEqI_1911_);
lean_inc(v_congrInfo_1910_);
lean_inc(v_getLevel_1909_);
lean_inc(v_inferType_1908_);
lean_inc(v_proofInstInfo_1907_);
lean_inc(v_maxFVar_1906_);
lean_inc(v_share_1905_);
lean_dec(v___x_1904_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1953_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1918_ = lean_box(0);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 8, v___x_1918_);
v___x_1920_ = v___x_1916_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_share_1905_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v_maxFVar_1906_);
lean_ctor_set(v_reuseFailAlloc_1952_, 2, v_proofInstInfo_1907_);
lean_ctor_set(v_reuseFailAlloc_1952_, 3, v_inferType_1908_);
lean_ctor_set(v_reuseFailAlloc_1952_, 4, v_getLevel_1909_);
lean_ctor_set(v_reuseFailAlloc_1952_, 5, v_congrInfo_1910_);
lean_ctor_set(v_reuseFailAlloc_1952_, 6, v_defEqI_1911_);
lean_ctor_set(v_reuseFailAlloc_1952_, 7, v_extensions_1912_);
lean_ctor_set(v_reuseFailAlloc_1952_, 8, v___x_1918_);
lean_ctor_set(v_reuseFailAlloc_1952_, 9, v_canon_1913_);
lean_ctor_set_uint8(v_reuseFailAlloc_1952_, sizeof(void*)*10, v_debug_1914_);
v___x_1920_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
lean_object* v___x_1921_; lean_object* v_issues_1922_; lean_object* v_r_1923_; 
v___x_1921_ = lean_st_ref_set(v_a_1897_, v___x_1920_);
v_issues_1922_ = lean_ctor_get(v___x_1903_, 8);
lean_inc(v_issues_1922_);
lean_dec(v___x_1903_);
lean_inc(v_a_1901_);
lean_inc_ref(v_a_1900_);
lean_inc(v_a_1899_);
lean_inc_ref(v_a_1898_);
lean_inc(v_a_1897_);
lean_inc_ref(v_a_1896_);
v_r_1923_ = lean_apply_7(v_x_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, lean_box(0));
if (lean_obj_tag(v_r_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1940_; 
v_a_1924_ = lean_ctor_get(v_r_1923_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v_r_1923_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1926_ = v_r_1923_;
v_isShared_1927_ = v_isSharedCheck_1940_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v_r_1923_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1940_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
lean_inc(v_a_1924_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set_tag(v___x_1926_, 1);
v___x_1929_ = v___x_1926_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1924_);
v___x_1929_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
lean_object* v___x_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
v___x_1930_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_1897_, v_issues_1922_, v___x_1929_);
lean_dec_ref(v___x_1929_);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1937_ == 0)
{
lean_object* v_unused_1938_; 
v_unused_1938_ = lean_ctor_get(v___x_1930_, 0);
lean_dec(v_unused_1938_);
v___x_1932_ = v___x_1930_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_dec(v___x_1930_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v_a_1924_);
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1924_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
v_a_1941_ = lean_ctor_get(v_r_1923_, 0);
lean_inc(v_a_1941_);
lean_dec_ref(v_r_1923_);
v___x_1942_ = lean_box(0);
v___x_1943_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(v_a_1897_, v_issues_1922_, v___x_1942_);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1950_ == 0)
{
lean_object* v_unused_1951_; 
v_unused_1951_ = lean_ctor_get(v___x_1943_, 0);
lean_dec(v_unused_1951_);
v___x_1945_ = v___x_1943_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_dec(v___x_1943_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
lean_ctor_set_tag(v___x_1945_, 1);
lean_ctor_set(v___x_1945_, 0, v_a_1941_);
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1941_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___redArg___boxed(lean_object* v_x_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_);
lean_dec(v_a_1961_);
lean_dec_ref(v_a_1960_);
lean_dec(v_a_1959_);
lean_dec_ref(v_a_1958_);
lean_dec(v_a_1957_);
lean_dec_ref(v_a_1956_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext(lean_object* v_00_u03b1_1964_, lean_object* v_x_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(v_x_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withNewIssueContext___boxed(lean_object* v_00_u03b1_1974_, lean_object* v_x_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_Meta_Sym_withNewIssueContext(v_00_u03b1_1974_, v_x_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
lean_dec(v_a_1977_);
lean_dec_ref(v_a_1976_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1984_, lean_object* v_vals_1985_, lean_object* v_i_1986_, lean_object* v_k_1987_){
_start:
{
uint8_t v___y_1989_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1995_ = lean_array_get_size(v_keys_1984_);
v___x_1996_ = lean_nat_dec_lt(v_i_1986_, v___x_1995_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; 
lean_dec(v_i_1986_);
v___x_1997_ = lean_box(0);
return v___x_1997_;
}
else
{
lean_object* v_fst_1998_; lean_object* v_snd_1999_; lean_object* v_k_x27_2000_; lean_object* v_fst_2001_; lean_object* v_snd_2002_; uint8_t v___x_2003_; 
v_fst_1998_ = lean_ctor_get(v_k_1987_, 0);
v_snd_1999_ = lean_ctor_get(v_k_1987_, 1);
v_k_x27_2000_ = lean_array_fget_borrowed(v_keys_1984_, v_i_1986_);
v_fst_2001_ = lean_ctor_get(v_k_x27_2000_, 0);
v_snd_2002_ = lean_ctor_get(v_k_x27_2000_, 1);
v___x_2003_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_1998_, v_fst_2001_);
if (v___x_2003_ == 0)
{
v___y_1989_ = v___x_2003_;
goto v___jp_1988_;
}
else
{
uint8_t v___x_2004_; 
v___x_2004_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_snd_1999_, v_snd_2002_);
v___y_1989_ = v___x_2004_;
goto v___jp_1988_;
}
}
v___jp_1988_:
{
if (v___y_1989_ == 0)
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = lean_unsigned_to_nat(1u);
v___x_1991_ = lean_nat_add(v_i_1986_, v___x_1990_);
lean_dec(v_i_1986_);
v_i_1986_ = v___x_1991_;
goto _start;
}
else
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = lean_array_fget_borrowed(v_vals_1985_, v_i_1986_);
lean_dec(v_i_1986_);
lean_inc(v___x_1993_);
v___x_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
return v___x_1994_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2005_, lean_object* v_vals_2006_, lean_object* v_i_2007_, lean_object* v_k_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_2005_, v_vals_2006_, v_i_2007_, v_k_2008_);
lean_dec_ref(v_k_2008_);
lean_dec_ref(v_vals_2006_);
lean_dec_ref(v_keys_2005_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(lean_object* v_x_2010_, size_t v_x_2011_, lean_object* v_x_2012_){
_start:
{
if (lean_obj_tag(v_x_2010_) == 0)
{
lean_object* v_es_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2041_; 
v_es_2013_ = lean_ctor_get(v_x_2010_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_x_2010_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2015_ = v_x_2010_;
v_isShared_2016_ = v_isSharedCheck_2041_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_es_2013_);
lean_dec(v_x_2010_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2041_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2017_; size_t v___x_2018_; size_t v___x_2019_; size_t v___x_2020_; lean_object* v_j_2021_; lean_object* v___x_2022_; 
v___x_2017_ = lean_box(2);
v___x_2018_ = ((size_t)5ULL);
v___x_2019_ = lean_usize_once(&l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1);
v___x_2020_ = lean_usize_land(v_x_2011_, v___x_2019_);
v_j_2021_ = lean_usize_to_nat(v___x_2020_);
v___x_2022_ = lean_array_get(v___x_2017_, v_es_2013_, v_j_2021_);
lean_dec(v_j_2021_);
lean_dec_ref(v_es_2013_);
switch(lean_obj_tag(v___x_2022_))
{
case 0:
{
lean_object* v_key_2023_; lean_object* v_val_2024_; uint8_t v___y_2026_; lean_object* v_fst_2031_; lean_object* v_snd_2032_; lean_object* v_fst_2033_; lean_object* v_snd_2034_; uint8_t v___x_2035_; 
v_key_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_key_2023_);
v_val_2024_ = lean_ctor_get(v___x_2022_, 1);
lean_inc(v_val_2024_);
lean_dec_ref(v___x_2022_);
v_fst_2031_ = lean_ctor_get(v_x_2012_, 0);
v_snd_2032_ = lean_ctor_get(v_x_2012_, 1);
v_fst_2033_ = lean_ctor_get(v_key_2023_, 0);
lean_inc(v_fst_2033_);
v_snd_2034_ = lean_ctor_get(v_key_2023_, 1);
lean_inc(v_snd_2034_);
lean_dec(v_key_2023_);
v___x_2035_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_2031_, v_fst_2033_);
lean_dec(v_fst_2033_);
if (v___x_2035_ == 0)
{
lean_dec(v_snd_2034_);
v___y_2026_ = v___x_2035_;
goto v___jp_2025_;
}
else
{
uint8_t v___x_2036_; 
v___x_2036_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_snd_2032_, v_snd_2034_);
lean_dec(v_snd_2034_);
v___y_2026_ = v___x_2036_;
goto v___jp_2025_;
}
v___jp_2025_:
{
if (v___y_2026_ == 0)
{
lean_object* v___x_2027_; 
lean_dec(v_val_2024_);
lean_del_object(v___x_2015_);
v___x_2027_ = lean_box(0);
return v___x_2027_;
}
else
{
lean_object* v___x_2029_; 
if (v_isShared_2016_ == 0)
{
lean_ctor_set_tag(v___x_2015_, 1);
lean_ctor_set(v___x_2015_, 0, v_val_2024_);
v___x_2029_ = v___x_2015_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_val_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
case 1:
{
lean_object* v_node_2037_; size_t v___x_2038_; 
lean_del_object(v___x_2015_);
v_node_2037_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_node_2037_);
lean_dec_ref(v___x_2022_);
v___x_2038_ = lean_usize_shift_right(v_x_2011_, v___x_2018_);
v_x_2010_ = v_node_2037_;
v_x_2011_ = v___x_2038_;
goto _start;
}
default: 
{
lean_object* v___x_2040_; 
lean_del_object(v___x_2015_);
v___x_2040_ = lean_box(0);
return v___x_2040_;
}
}
}
}
else
{
lean_object* v_ks_2042_; lean_object* v_vs_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v_ks_2042_ = lean_ctor_get(v_x_2010_, 0);
lean_inc_ref(v_ks_2042_);
v_vs_2043_ = lean_ctor_get(v_x_2010_, 1);
lean_inc_ref(v_vs_2043_);
lean_dec_ref(v_x_2010_);
v___x_2044_ = lean_unsigned_to_nat(0u);
v___x_2045_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_ks_2042_, v_vs_2043_, v___x_2044_, v_x_2012_);
lean_dec_ref(v_vs_2043_);
lean_dec_ref(v_ks_2042_);
return v___x_2045_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg___boxed(lean_object* v_x_2046_, lean_object* v_x_2047_, lean_object* v_x_2048_){
_start:
{
size_t v_x_2775__boxed_2049_; lean_object* v_res_2050_; 
v_x_2775__boxed_2049_ = lean_unbox_usize(v_x_2047_);
lean_dec(v_x_2047_);
v_res_2050_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_2046_, v_x_2775__boxed_2049_, v_x_2048_);
lean_dec_ref(v_x_2048_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(lean_object* v_x_2051_, lean_object* v_x_2052_){
_start:
{
lean_object* v_fst_2053_; lean_object* v_snd_2054_; uint64_t v___x_2055_; uint64_t v___x_2056_; uint64_t v___x_2057_; size_t v___x_2058_; lean_object* v___x_2059_; 
v_fst_2053_ = lean_ctor_get(v_x_2052_, 0);
v_snd_2054_ = lean_ctor_get(v_x_2052_, 1);
v___x_2055_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_2053_);
v___x_2056_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_snd_2054_);
v___x_2057_ = lean_uint64_mix_hash(v___x_2055_, v___x_2056_);
v___x_2058_ = lean_uint64_to_usize(v___x_2057_);
v___x_2059_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_2051_, v___x_2058_, v_x_2052_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg___boxed(lean_object* v_x_2060_, lean_object* v_x_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_2060_, v_x_2061_);
lean_dec_ref(v_x_2061_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2063_, lean_object* v_x_2064_, lean_object* v_x_2065_, lean_object* v_x_2066_){
_start:
{
lean_object* v_ks_2067_; lean_object* v_vs_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2097_; 
v_ks_2067_ = lean_ctor_get(v_x_2063_, 0);
v_vs_2068_ = lean_ctor_get(v_x_2063_, 1);
v_isSharedCheck_2097_ = !lean_is_exclusive(v_x_2063_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2070_ = v_x_2063_;
v_isShared_2071_ = v_isSharedCheck_2097_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_vs_2068_);
lean_inc(v_ks_2067_);
lean_dec(v_x_2063_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2097_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
uint8_t v___y_2073_; lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_2085_ = lean_array_get_size(v_ks_2067_);
v___x_2086_ = lean_nat_dec_lt(v_x_2064_, v___x_2085_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
lean_del_object(v___x_2070_);
lean_dec(v_x_2064_);
v___x_2087_ = lean_array_push(v_ks_2067_, v_x_2065_);
v___x_2088_ = lean_array_push(v_vs_2068_, v_x_2066_);
v___x_2089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2087_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
return v___x_2089_;
}
else
{
lean_object* v_fst_2090_; lean_object* v_snd_2091_; lean_object* v_k_x27_2092_; lean_object* v_fst_2093_; lean_object* v_snd_2094_; uint8_t v___x_2095_; 
v_fst_2090_ = lean_ctor_get(v_x_2065_, 0);
v_snd_2091_ = lean_ctor_get(v_x_2065_, 1);
v_k_x27_2092_ = lean_array_fget_borrowed(v_ks_2067_, v_x_2064_);
v_fst_2093_ = lean_ctor_get(v_k_x27_2092_, 0);
v_snd_2094_ = lean_ctor_get(v_k_x27_2092_, 1);
v___x_2095_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_2090_, v_fst_2093_);
if (v___x_2095_ == 0)
{
v___y_2073_ = v___x_2095_;
goto v___jp_2072_;
}
else
{
uint8_t v___x_2096_; 
v___x_2096_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_snd_2091_, v_snd_2094_);
v___y_2073_ = v___x_2096_;
goto v___jp_2072_;
}
}
v___jp_2072_:
{
if (v___y_2073_ == 0)
{
lean_object* v___x_2075_; 
if (v_isShared_2071_ == 0)
{
v___x_2075_ = v___x_2070_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_ks_2067_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v_vs_2068_);
v___x_2075_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = lean_unsigned_to_nat(1u);
v___x_2077_ = lean_nat_add(v_x_2064_, v___x_2076_);
lean_dec(v_x_2064_);
v_x_2063_ = v___x_2075_;
v_x_2064_ = v___x_2077_;
goto _start;
}
}
else
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2080_ = lean_array_fset(v_ks_2067_, v_x_2064_, v_x_2065_);
v___x_2081_ = lean_array_fset(v_vs_2068_, v_x_2064_, v_x_2066_);
lean_dec(v_x_2064_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 1, v___x_2081_);
lean_ctor_set(v___x_2070_, 0, v___x_2080_);
v___x_2083_ = v___x_2070_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2080_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(lean_object* v_n_2098_, lean_object* v_k_2099_, lean_object* v_v_2100_){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = lean_unsigned_to_nat(0u);
v___x_2102_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_n_2098_, v___x_2101_, v_k_2099_, v_v_2100_);
return v___x_2102_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2103_; 
v___x_2103_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(lean_object* v_x_2104_, size_t v_x_2105_, size_t v_x_2106_, lean_object* v_x_2107_, lean_object* v_x_2108_){
_start:
{
if (lean_obj_tag(v_x_2104_) == 0)
{
lean_object* v_es_2109_; size_t v___x_2110_; size_t v___x_2111_; size_t v___x_2112_; size_t v___x_2113_; lean_object* v_j_2114_; lean_object* v___x_2115_; uint8_t v___x_2116_; 
v_es_2109_ = lean_ctor_get(v_x_2104_, 0);
v___x_2110_ = ((size_t)5ULL);
v___x_2111_ = ((size_t)1ULL);
v___x_2112_ = lean_usize_once(&l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1);
v___x_2113_ = lean_usize_land(v_x_2105_, v___x_2112_);
v_j_2114_ = lean_usize_to_nat(v___x_2113_);
v___x_2115_ = lean_array_get_size(v_es_2109_);
v___x_2116_ = lean_nat_dec_lt(v_j_2114_, v___x_2115_);
if (v___x_2116_ == 0)
{
lean_dec(v_j_2114_);
lean_dec(v_x_2108_);
lean_dec_ref(v_x_2107_);
return v_x_2104_;
}
else
{
lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2160_; 
lean_inc_ref(v_es_2109_);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_x_2104_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; 
v_unused_2161_ = lean_ctor_get(v_x_2104_, 0);
lean_dec(v_unused_2161_);
v___x_2118_ = v_x_2104_;
v_isShared_2119_ = v_isSharedCheck_2160_;
goto v_resetjp_2117_;
}
else
{
lean_dec(v_x_2104_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2160_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v_v_2120_; lean_object* v___x_2121_; lean_object* v_xs_x27_2122_; lean_object* v___y_2124_; 
v_v_2120_ = lean_array_fget(v_es_2109_, v_j_2114_);
v___x_2121_ = lean_box(0);
v_xs_x27_2122_ = lean_array_fset(v_es_2109_, v_j_2114_, v___x_2121_);
switch(lean_obj_tag(v_v_2120_))
{
case 0:
{
lean_object* v_key_2129_; lean_object* v_val_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2147_; 
v_key_2129_ = lean_ctor_get(v_v_2120_, 0);
v_val_2130_ = lean_ctor_get(v_v_2120_, 1);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_v_2120_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2132_ = v_v_2120_;
v_isShared_2133_ = v_isSharedCheck_2147_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_val_2130_);
lean_inc(v_key_2129_);
lean_dec(v_v_2120_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2147_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
uint8_t v___y_2135_; lean_object* v_fst_2141_; lean_object* v_snd_2142_; lean_object* v_fst_2143_; lean_object* v_snd_2144_; uint8_t v___x_2145_; 
v_fst_2141_ = lean_ctor_get(v_x_2107_, 0);
v_snd_2142_ = lean_ctor_get(v_x_2107_, 1);
v_fst_2143_ = lean_ctor_get(v_key_2129_, 0);
v_snd_2144_ = lean_ctor_get(v_key_2129_, 1);
v___x_2145_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_2141_, v_fst_2143_);
if (v___x_2145_ == 0)
{
v___y_2135_ = v___x_2145_;
goto v___jp_2134_;
}
else
{
uint8_t v___x_2146_; 
v___x_2146_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_snd_2142_, v_snd_2144_);
v___y_2135_ = v___x_2146_;
goto v___jp_2134_;
}
v___jp_2134_:
{
if (v___y_2135_ == 0)
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
lean_del_object(v___x_2132_);
v___x_2136_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2129_, v_val_2130_, v_x_2107_, v_x_2108_);
v___x_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2136_);
v___y_2124_ = v___x_2137_;
goto v___jp_2123_;
}
else
{
lean_object* v___x_2139_; 
lean_dec(v_val_2130_);
lean_dec(v_key_2129_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 1, v_x_2108_);
lean_ctor_set(v___x_2132_, 0, v_x_2107_);
v___x_2139_ = v___x_2132_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_x_2107_);
lean_ctor_set(v_reuseFailAlloc_2140_, 1, v_x_2108_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
v___y_2124_ = v___x_2139_;
goto v___jp_2123_;
}
}
}
}
}
case 1:
{
lean_object* v_node_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2158_; 
v_node_2148_ = lean_ctor_get(v_v_2120_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_v_2120_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2150_ = v_v_2120_;
v_isShared_2151_ = v_isSharedCheck_2158_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_node_2148_);
lean_dec(v_v_2120_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2158_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
size_t v___x_2152_; size_t v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2156_; 
v___x_2152_ = lean_usize_shift_right(v_x_2105_, v___x_2110_);
v___x_2153_ = lean_usize_add(v_x_2106_, v___x_2111_);
v___x_2154_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_node_2148_, v___x_2152_, v___x_2153_, v_x_2107_, v_x_2108_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 0, v___x_2154_);
v___x_2156_ = v___x_2150_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
v___y_2124_ = v___x_2156_;
goto v___jp_2123_;
}
}
}
default: 
{
lean_object* v___x_2159_; 
v___x_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2159_, 0, v_x_2107_);
lean_ctor_set(v___x_2159_, 1, v_x_2108_);
v___y_2124_ = v___x_2159_;
goto v___jp_2123_;
}
}
v___jp_2123_:
{
lean_object* v___x_2125_; lean_object* v___x_2127_; 
v___x_2125_ = lean_array_fset(v_xs_x27_2122_, v_j_2114_, v___y_2124_);
lean_dec(v_j_2114_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2125_);
v___x_2127_ = v___x_2118_;
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
}
else
{
lean_object* v_ks_2162_; lean_object* v_vs_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2183_; 
v_ks_2162_ = lean_ctor_get(v_x_2104_, 0);
v_vs_2163_ = lean_ctor_get(v_x_2104_, 1);
v_isSharedCheck_2183_ = !lean_is_exclusive(v_x_2104_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2165_ = v_x_2104_;
v_isShared_2166_ = v_isSharedCheck_2183_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_vs_2163_);
lean_inc(v_ks_2162_);
lean_dec(v_x_2104_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2183_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_ks_2162_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_vs_2163_);
v___x_2168_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v_newNode_2169_; uint8_t v___y_2171_; size_t v___x_2177_; uint8_t v___x_2178_; 
v_newNode_2169_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v___x_2168_, v_x_2107_, v_x_2108_);
v___x_2177_ = ((size_t)7ULL);
v___x_2178_ = lean_usize_dec_le(v___x_2177_, v_x_2106_);
if (v___x_2178_ == 0)
{
lean_object* v___x_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; 
v___x_2179_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2169_);
v___x_2180_ = lean_unsigned_to_nat(4u);
v___x_2181_ = lean_nat_dec_lt(v___x_2179_, v___x_2180_);
lean_dec(v___x_2179_);
v___y_2171_ = v___x_2181_;
goto v___jp_2170_;
}
else
{
v___y_2171_ = v___x_2178_;
goto v___jp_2170_;
}
v___jp_2170_:
{
if (v___y_2171_ == 0)
{
lean_object* v_ks_2172_; lean_object* v_vs_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v_ks_2172_ = lean_ctor_get(v_newNode_2169_, 0);
lean_inc_ref(v_ks_2172_);
v_vs_2173_ = lean_ctor_get(v_newNode_2169_, 1);
lean_inc_ref(v_vs_2173_);
lean_dec_ref(v_newNode_2169_);
v___x_2174_ = lean_unsigned_to_nat(0u);
v___x_2175_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0);
v___x_2176_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_x_2106_, v_ks_2172_, v_vs_2173_, v___x_2174_, v___x_2175_);
lean_dec_ref(v_vs_2173_);
lean_dec_ref(v_ks_2172_);
return v___x_2176_;
}
else
{
return v_newNode_2169_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(size_t v_depth_2184_, lean_object* v_keys_2185_, lean_object* v_vals_2186_, lean_object* v_i_2187_, lean_object* v_entries_2188_){
_start:
{
lean_object* v___x_2189_; uint8_t v___x_2190_; 
v___x_2189_ = lean_array_get_size(v_keys_2185_);
v___x_2190_ = lean_nat_dec_lt(v_i_2187_, v___x_2189_);
if (v___x_2190_ == 0)
{
lean_dec(v_i_2187_);
return v_entries_2188_;
}
else
{
lean_object* v_k_2191_; lean_object* v_fst_2192_; lean_object* v_snd_2193_; lean_object* v_v_2194_; uint64_t v___x_2195_; uint64_t v___x_2196_; uint64_t v___x_2197_; size_t v_h_2198_; size_t v___x_2199_; lean_object* v___x_2200_; size_t v___x_2201_; size_t v___x_2202_; size_t v___x_2203_; size_t v_h_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v_k_2191_ = lean_array_fget_borrowed(v_keys_2185_, v_i_2187_);
v_fst_2192_ = lean_ctor_get(v_k_2191_, 0);
v_snd_2193_ = lean_ctor_get(v_k_2191_, 1);
v_v_2194_ = lean_array_fget_borrowed(v_vals_2186_, v_i_2187_);
v___x_2195_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_2192_);
v___x_2196_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_snd_2193_);
v___x_2197_ = lean_uint64_mix_hash(v___x_2195_, v___x_2196_);
v_h_2198_ = lean_uint64_to_usize(v___x_2197_);
v___x_2199_ = ((size_t)5ULL);
v___x_2200_ = lean_unsigned_to_nat(1u);
v___x_2201_ = ((size_t)1ULL);
v___x_2202_ = lean_usize_sub(v_depth_2184_, v___x_2201_);
v___x_2203_ = lean_usize_mul(v___x_2199_, v___x_2202_);
v_h_2204_ = lean_usize_shift_right(v_h_2198_, v___x_2203_);
v___x_2205_ = lean_nat_add(v_i_2187_, v___x_2200_);
lean_dec(v_i_2187_);
lean_inc(v_v_2194_);
lean_inc(v_k_2191_);
v___x_2206_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_entries_2188_, v_h_2204_, v_depth_2184_, v_k_2191_, v_v_2194_);
v_i_2187_ = v___x_2205_;
v_entries_2188_ = v___x_2206_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_2208_, lean_object* v_keys_2209_, lean_object* v_vals_2210_, lean_object* v_i_2211_, lean_object* v_entries_2212_){
_start:
{
size_t v_depth_boxed_2213_; lean_object* v_res_2214_; 
v_depth_boxed_2213_ = lean_unbox_usize(v_depth_2208_);
lean_dec(v_depth_2208_);
v_res_2214_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_boxed_2213_, v_keys_2209_, v_vals_2210_, v_i_2211_, v_entries_2212_);
lean_dec_ref(v_vals_2210_);
lean_dec_ref(v_keys_2209_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___boxed(lean_object* v_x_2215_, lean_object* v_x_2216_, lean_object* v_x_2217_, lean_object* v_x_2218_, lean_object* v_x_2219_){
_start:
{
size_t v_x_2966__boxed_2220_; size_t v_x_2967__boxed_2221_; lean_object* v_res_2222_; 
v_x_2966__boxed_2220_ = lean_unbox_usize(v_x_2216_);
lean_dec(v_x_2216_);
v_x_2967__boxed_2221_ = lean_unbox_usize(v_x_2217_);
lean_dec(v_x_2217_);
v_res_2222_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_2215_, v_x_2966__boxed_2220_, v_x_2967__boxed_2221_, v_x_2218_, v_x_2219_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(lean_object* v_x_2223_, lean_object* v_x_2224_, lean_object* v_x_2225_){
_start:
{
lean_object* v_fst_2226_; lean_object* v_snd_2227_; uint64_t v___x_2228_; uint64_t v___x_2229_; uint64_t v___x_2230_; size_t v___x_2231_; size_t v___x_2232_; lean_object* v___x_2233_; 
v_fst_2226_ = lean_ctor_get(v_x_2224_, 0);
v_snd_2227_ = lean_ctor_get(v_x_2224_, 1);
v___x_2228_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_2226_);
v___x_2229_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_snd_2227_);
v___x_2230_ = lean_uint64_mix_hash(v___x_2228_, v___x_2229_);
v___x_2231_ = lean_uint64_to_usize(v___x_2230_);
v___x_2232_ = ((size_t)1ULL);
v___x_2233_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_2223_, v___x_2231_, v___x_2232_, v_x_2224_, v_x_2225_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object* v_s_2234_, lean_object* v_t_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v___x_2242_; lean_object* v_defEqI_2243_; lean_object* v_key_2244_; lean_object* v___x_2245_; 
v___x_2242_ = lean_st_ref_get(v_a_2236_);
v_defEqI_2243_ = lean_ctor_get(v___x_2242_, 6);
lean_inc_ref(v_defEqI_2243_);
lean_dec(v___x_2242_);
lean_inc_ref(v_t_2235_);
lean_inc_ref(v_s_2234_);
v_key_2244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_2244_, 0, v_s_2234_);
lean_ctor_set(v_key_2244_, 1, v_t_2235_);
v___x_2245_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_defEqI_2243_, v_key_2244_);
if (lean_obj_tag(v___x_2245_) == 1)
{
lean_object* v_val_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_dec_ref(v_key_2244_);
lean_dec_ref(v_t_2235_);
lean_dec_ref(v_s_2234_);
v_val_2246_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2245_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_val_2246_);
lean_dec(v___x_2245_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
lean_ctor_set_tag(v___x_2248_, 0);
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_val_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
else
{
lean_object* v___x_2254_; 
lean_dec(v___x_2245_);
v___x_2254_ = l_Lean_Meta_isDefEqI(v_s_2234_, v_t_2235_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2283_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2257_ = v___x_2254_;
v_isShared_2258_ = v_isSharedCheck_2283_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2254_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2283_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2259_; lean_object* v_share_2260_; lean_object* v_maxFVar_2261_; lean_object* v_proofInstInfo_2262_; lean_object* v_inferType_2263_; lean_object* v_getLevel_2264_; lean_object* v_congrInfo_2265_; lean_object* v_defEqI_2266_; lean_object* v_extensions_2267_; lean_object* v_issues_2268_; lean_object* v_canon_2269_; uint8_t v_debug_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2282_; 
v___x_2259_ = lean_st_ref_take(v_a_2236_);
v_share_2260_ = lean_ctor_get(v___x_2259_, 0);
v_maxFVar_2261_ = lean_ctor_get(v___x_2259_, 1);
v_proofInstInfo_2262_ = lean_ctor_get(v___x_2259_, 2);
v_inferType_2263_ = lean_ctor_get(v___x_2259_, 3);
v_getLevel_2264_ = lean_ctor_get(v___x_2259_, 4);
v_congrInfo_2265_ = lean_ctor_get(v___x_2259_, 5);
v_defEqI_2266_ = lean_ctor_get(v___x_2259_, 6);
v_extensions_2267_ = lean_ctor_get(v___x_2259_, 7);
v_issues_2268_ = lean_ctor_get(v___x_2259_, 8);
v_canon_2269_ = lean_ctor_get(v___x_2259_, 9);
v_debug_2270_ = lean_ctor_get_uint8(v___x_2259_, sizeof(void*)*10);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2272_ = v___x_2259_;
v_isShared_2273_ = v_isSharedCheck_2282_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_canon_2269_);
lean_inc(v_issues_2268_);
lean_inc(v_extensions_2267_);
lean_inc(v_defEqI_2266_);
lean_inc(v_congrInfo_2265_);
lean_inc(v_getLevel_2264_);
lean_inc(v_inferType_2263_);
lean_inc(v_proofInstInfo_2262_);
lean_inc(v_maxFVar_2261_);
lean_inc(v_share_2260_);
lean_dec(v___x_2259_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2282_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2274_; lean_object* v___x_2276_; 
lean_inc(v_a_2255_);
v___x_2274_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_defEqI_2266_, v_key_2244_, v_a_2255_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 6, v___x_2274_);
v___x_2276_ = v___x_2272_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_share_2260_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v_maxFVar_2261_);
lean_ctor_set(v_reuseFailAlloc_2281_, 2, v_proofInstInfo_2262_);
lean_ctor_set(v_reuseFailAlloc_2281_, 3, v_inferType_2263_);
lean_ctor_set(v_reuseFailAlloc_2281_, 4, v_getLevel_2264_);
lean_ctor_set(v_reuseFailAlloc_2281_, 5, v_congrInfo_2265_);
lean_ctor_set(v_reuseFailAlloc_2281_, 6, v___x_2274_);
lean_ctor_set(v_reuseFailAlloc_2281_, 7, v_extensions_2267_);
lean_ctor_set(v_reuseFailAlloc_2281_, 8, v_issues_2268_);
lean_ctor_set(v_reuseFailAlloc_2281_, 9, v_canon_2269_);
lean_ctor_set_uint8(v_reuseFailAlloc_2281_, sizeof(void*)*10, v_debug_2270_);
v___x_2276_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
lean_object* v___x_2277_; lean_object* v___x_2279_; 
v___x_2277_ = lean_st_ref_set(v_a_2236_, v___x_2276_);
if (v_isShared_2258_ == 0)
{
v___x_2279_ = v___x_2257_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2255_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
}
else
{
lean_dec_ref(v_key_2244_);
return v___x_2254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___redArg___boxed(lean_object* v_s_2284_, lean_object* v_t_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_2284_, v_t_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
lean_dec(v_a_2290_);
lean_dec_ref(v_a_2289_);
lean_dec(v_a_2288_);
lean_dec_ref(v_a_2287_);
lean_dec(v_a_2286_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI(lean_object* v_s_2293_, lean_object* v_t_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_s_2293_, v_t_2294_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isDefEqI___boxed(lean_object* v_s_2303_, lean_object* v_t_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Lean_Meta_Sym_isDefEqI(v_s_2303_, v_t_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_);
lean_dec(v_a_2310_);
lean_dec_ref(v_a_2309_);
lean_dec(v_a_2308_);
lean_dec_ref(v_a_2307_);
lean_dec(v_a_2306_);
lean_dec_ref(v_a_2305_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(lean_object* v_00_u03b2_2313_, lean_object* v_x_2314_, lean_object* v_x_2315_){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_x_2314_, v_x_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___boxed(lean_object* v_00_u03b2_2317_, lean_object* v_x_2318_, lean_object* v_x_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(v_00_u03b2_2317_, v_x_2318_, v_x_2319_);
lean_dec_ref(v_x_2319_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1(lean_object* v_00_u03b2_2321_, lean_object* v_x_2322_, lean_object* v_x_2323_, lean_object* v_x_2324_){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_x_2322_, v_x_2323_, v_x_2324_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(lean_object* v_00_u03b2_2326_, lean_object* v_x_2327_, size_t v_x_2328_, lean_object* v_x_2329_){
_start:
{
lean_object* v___x_2330_; 
v___x_2330_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_2327_, v_x_2328_, v_x_2329_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2331_, lean_object* v_x_2332_, lean_object* v_x_2333_, lean_object* v_x_2334_){
_start:
{
size_t v_x_3245__boxed_2335_; lean_object* v_res_2336_; 
v_x_3245__boxed_2335_ = lean_unbox_usize(v_x_2333_);
lean_dec(v_x_2333_);
v_res_2336_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(v_00_u03b2_2331_, v_x_2332_, v_x_3245__boxed_2335_, v_x_2334_);
lean_dec_ref(v_x_2334_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(lean_object* v_00_u03b2_2337_, lean_object* v_x_2338_, size_t v_x_2339_, size_t v_x_2340_, lean_object* v_x_2341_, lean_object* v_x_2342_){
_start:
{
lean_object* v___x_2343_; 
v___x_2343_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_2338_, v_x_2339_, v_x_2340_, v_x_2341_, v_x_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2344_, lean_object* v_x_2345_, lean_object* v_x_2346_, lean_object* v_x_2347_, lean_object* v_x_2348_, lean_object* v_x_2349_){
_start:
{
size_t v_x_3256__boxed_2350_; size_t v_x_3257__boxed_2351_; lean_object* v_res_2352_; 
v_x_3256__boxed_2350_ = lean_unbox_usize(v_x_2346_);
lean_dec(v_x_2346_);
v_x_3257__boxed_2351_ = lean_unbox_usize(v_x_2347_);
lean_dec(v_x_2347_);
v_res_2352_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(v_00_u03b2_2344_, v_x_2345_, v_x_3256__boxed_2350_, v_x_3257__boxed_2351_, v_x_2348_, v_x_2349_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2353_, lean_object* v_keys_2354_, lean_object* v_vals_2355_, lean_object* v_heq_2356_, lean_object* v_i_2357_, lean_object* v_k_2358_){
_start:
{
lean_object* v___x_2359_; 
v___x_2359_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_2354_, v_vals_2355_, v_i_2357_, v_k_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2360_, lean_object* v_keys_2361_, lean_object* v_vals_2362_, lean_object* v_heq_2363_, lean_object* v_i_2364_, lean_object* v_k_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(v_00_u03b2_2360_, v_keys_2361_, v_vals_2362_, v_heq_2363_, v_i_2364_, v_k_2365_);
lean_dec_ref(v_k_2365_);
lean_dec_ref(v_vals_2362_);
lean_dec_ref(v_keys_2361_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2367_, lean_object* v_n_2368_, lean_object* v_k_2369_, lean_object* v_v_2370_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v_n_2368_, v_k_2369_, v_v_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_2372_, size_t v_depth_2373_, lean_object* v_keys_2374_, lean_object* v_vals_2375_, lean_object* v_heq_2376_, lean_object* v_i_2377_, lean_object* v_entries_2378_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_2373_, v_keys_2374_, v_vals_2375_, v_i_2377_, v_entries_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2380_, lean_object* v_depth_2381_, lean_object* v_keys_2382_, lean_object* v_vals_2383_, lean_object* v_heq_2384_, lean_object* v_i_2385_, lean_object* v_entries_2386_){
_start:
{
size_t v_depth_boxed_2387_; lean_object* v_res_2388_; 
v_depth_boxed_2387_ = lean_unbox_usize(v_depth_2381_);
lean_dec(v_depth_2381_);
v_res_2388_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(v_00_u03b2_2380_, v_depth_boxed_2387_, v_keys_2382_, v_vals_2383_, v_heq_2384_, v_i_2385_, v_entries_2386_);
lean_dec_ref(v_vals_2383_);
lean_dec_ref(v_keys_2382_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2389_, lean_object* v_x_2390_, lean_object* v_x_2391_, lean_object* v_x_2392_, lean_object* v_x_2393_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_x_2390_, v_x_2391_, v_x_2392_, v_x_2393_);
return v___x_2394_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0(void){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = l_instMonadEIO(lean_box(0));
return v___x_2395_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__1(void){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__0, &l_Lean_Meta_Sym_instInhabitedSymM___closed__0_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0);
v___x_2397_ = l_StateRefT_x27_instMonad___redArg(v___x_2396_);
return v___x_2397_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__6(void){
_start:
{
lean_object* v___x_2402_; lean_object* v___f_2403_; 
v___x_2402_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_2403_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2403_, 0, v___x_2402_);
return v___f_2403_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__7(void){
_start:
{
lean_object* v___x_2404_; lean_object* v___f_2405_; 
v___x_2404_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_2405_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2405_, 0, v___x_2404_);
return v___f_2405_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8(void){
_start:
{
lean_object* v___f_2406_; lean_object* v___f_2407_; lean_object* v___x_2408_; 
v___f_2406_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__7, &l_Lean_Meta_Sym_instInhabitedSymM___closed__7_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__7);
v___f_2407_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__6, &l_Lean_Meta_Sym_instInhabitedSymM___closed__6_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__6);
v___x_2408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2408_, 0, v___f_2407_);
lean_ctor_set(v___x_2408_, 1, v___f_2406_);
return v___x_2408_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__9(void){
_start:
{
lean_object* v___x_2409_; lean_object* v___f_2410_; 
v___x_2409_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__8, &l_Lean_Meta_Sym_instInhabitedSymM___closed__8_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8);
v___f_2410_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2410_, 0, v___x_2409_);
return v___f_2410_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__10(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___f_2412_; 
v___x_2411_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__8, &l_Lean_Meta_Sym_instInhabitedSymM___closed__8_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8);
v___f_2412_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2412_, 0, v___x_2411_);
return v___f_2412_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__11(void){
_start:
{
lean_object* v___f_2413_; lean_object* v___f_2414_; lean_object* v___x_2415_; 
v___f_2413_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__10, &l_Lean_Meta_Sym_instInhabitedSymM___closed__10_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__10);
v___f_2414_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__9, &l_Lean_Meta_Sym_instInhabitedSymM___closed__9_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__9);
v___x_2415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___f_2414_);
lean_ctor_set(v___x_2415_, 1, v___f_2413_);
return v___x_2415_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__12(void){
_start:
{
lean_object* v___x_2416_; lean_object* v___f_2417_; 
v___x_2416_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__11, &l_Lean_Meta_Sym_instInhabitedSymM___closed__11_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__11);
v___f_2417_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2417_, 0, v___x_2416_);
return v___f_2417_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__13(void){
_start:
{
lean_object* v___x_2418_; lean_object* v___f_2419_; 
v___x_2418_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__11, &l_Lean_Meta_Sym_instInhabitedSymM___closed__11_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__11);
v___f_2419_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2419_, 0, v___x_2418_);
return v___f_2419_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__14(void){
_start:
{
lean_object* v___f_2420_; lean_object* v___f_2421_; lean_object* v___x_2422_; 
v___f_2420_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__13, &l_Lean_Meta_Sym_instInhabitedSymM___closed__13_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__13);
v___f_2421_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__12, &l_Lean_Meta_Sym_instInhabitedSymM___closed__12_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__12);
v___x_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___f_2421_);
lean_ctor_set(v___x_2422_, 1, v___f_2420_);
return v___x_2422_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__15(void){
_start:
{
lean_object* v___x_2423_; lean_object* v___f_2424_; 
v___x_2423_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__14, &l_Lean_Meta_Sym_instInhabitedSymM___closed__14_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__14);
v___f_2424_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2424_, 0, v___x_2423_);
return v___f_2424_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__16(void){
_start:
{
lean_object* v___x_2425_; lean_object* v___f_2426_; 
v___x_2425_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__14, &l_Lean_Meta_Sym_instInhabitedSymM___closed__14_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__14);
v___f_2426_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2426_, 0, v___x_2425_);
return v___f_2426_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__17(void){
_start:
{
lean_object* v___f_2427_; lean_object* v___f_2428_; lean_object* v___x_2429_; 
v___f_2427_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__16, &l_Lean_Meta_Sym_instInhabitedSymM___closed__16_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__16);
v___f_2428_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__15, &l_Lean_Meta_Sym_instInhabitedSymM___closed__15_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__15);
v___x_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___f_2428_);
lean_ctor_set(v___x_2429_, 1, v___f_2427_);
return v___x_2429_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__22(void){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2434_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2435_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__21));
v___x_2436_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__20));
v___x_2437_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2436_, v___x_2435_, v___x_2434_);
return v___x_2437_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__23(void){
_start:
{
lean_object* v___x_2438_; lean_object* v___f_2439_; lean_object* v___f_2440_; lean_object* v___x_2441_; 
v___x_2438_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__22, &l_Lean_Meta_Sym_instInhabitedSymM___closed__22_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__22);
v___f_2439_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__19));
v___f_2440_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__18));
v___x_2441_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2440_, v___f_2439_, v___x_2438_);
return v___x_2441_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__24(void){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2442_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__23, &l_Lean_Meta_Sym_instInhabitedSymM___closed__23_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__23);
v___x_2443_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__21));
v___x_2444_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__20));
v___x_2445_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2444_, v___x_2443_, v___x_2442_);
return v___x_2445_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__25(void){
_start:
{
lean_object* v___x_2446_; lean_object* v___f_2447_; lean_object* v___f_2448_; lean_object* v___x_2449_; 
v___x_2446_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__24, &l_Lean_Meta_Sym_instInhabitedSymM___closed__24_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__24);
v___f_2447_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__19));
v___f_2448_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__18));
v___x_2449_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2448_, v___f_2447_, v___x_2446_);
return v___x_2449_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__26(void){
_start:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___f_2452_; 
v___x_2450_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__21));
v___x_2451_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2452_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2452_, 0, v___x_2451_);
lean_closure_set(v___f_2452_, 1, v___x_2450_);
return v___f_2452_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__27(void){
_start:
{
lean_object* v___f_2453_; lean_object* v___f_2454_; lean_object* v___f_2455_; 
v___f_2453_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__19));
v___f_2454_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__26, &l_Lean_Meta_Sym_instInhabitedSymM___closed__26_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__26);
v___f_2455_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2455_, 0, v___f_2454_);
lean_closure_set(v___f_2455_, 1, v___f_2453_);
return v___f_2455_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__29(void){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__28));
v___x_2458_ = l_Lean_stringToMessageData(v___x_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object* v_00_u03b1_2459_){
_start:
{
lean_object* v___x_2460_; lean_object* v_toApplicative_2461_; lean_object* v_toFunctor_2462_; lean_object* v_toSeq_2463_; lean_object* v_toSeqLeft_2464_; lean_object* v_toSeqRight_2465_; lean_object* v___f_2466_; lean_object* v___f_2467_; lean_object* v___f_2468_; lean_object* v___f_2469_; lean_object* v___x_2470_; lean_object* v___f_2471_; lean_object* v___f_2472_; lean_object* v___f_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v_toApplicative_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2514_; 
v___x_2460_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__1, &l_Lean_Meta_Sym_instInhabitedSymM___closed__1_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__1);
v_toApplicative_2461_ = lean_ctor_get(v___x_2460_, 0);
v_toFunctor_2462_ = lean_ctor_get(v_toApplicative_2461_, 0);
v_toSeq_2463_ = lean_ctor_get(v_toApplicative_2461_, 2);
v_toSeqLeft_2464_ = lean_ctor_get(v_toApplicative_2461_, 3);
v_toSeqRight_2465_ = lean_ctor_get(v_toApplicative_2461_, 4);
v___f_2466_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__2));
v___f_2467_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__3));
lean_inc_ref_n(v_toFunctor_2462_, 2);
v___f_2468_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2468_, 0, v_toFunctor_2462_);
v___f_2469_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2469_, 0, v_toFunctor_2462_);
v___x_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___f_2468_);
lean_ctor_set(v___x_2470_, 1, v___f_2469_);
lean_inc(v_toSeqRight_2465_);
v___f_2471_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2471_, 0, v_toSeqRight_2465_);
lean_inc(v_toSeqLeft_2464_);
v___f_2472_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2472_, 0, v_toSeqLeft_2464_);
lean_inc(v_toSeq_2463_);
v___f_2473_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2473_, 0, v_toSeq_2463_);
v___x_2474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2470_);
lean_ctor_set(v___x_2474_, 1, v___f_2466_);
lean_ctor_set(v___x_2474_, 2, v___f_2473_);
lean_ctor_set(v___x_2474_, 3, v___f_2472_);
lean_ctor_set(v___x_2474_, 4, v___f_2471_);
v___x_2475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2474_);
lean_ctor_set(v___x_2475_, 1, v___f_2467_);
v___x_2476_ = l_StateRefT_x27_instMonad___redArg(v___x_2475_);
v_toApplicative_2477_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2514_ == 0)
{
lean_object* v_unused_2515_; 
v_unused_2515_ = lean_ctor_get(v___x_2476_, 1);
lean_dec(v_unused_2515_);
v___x_2479_ = v___x_2476_;
v_isShared_2480_ = v_isSharedCheck_2514_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_toApplicative_2477_);
lean_dec(v___x_2476_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2514_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v_toFunctor_2481_; lean_object* v_toSeq_2482_; lean_object* v_toSeqLeft_2483_; lean_object* v_toSeqRight_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2512_; 
v_toFunctor_2481_ = lean_ctor_get(v_toApplicative_2477_, 0);
v_toSeq_2482_ = lean_ctor_get(v_toApplicative_2477_, 2);
v_toSeqLeft_2483_ = lean_ctor_get(v_toApplicative_2477_, 3);
v_toSeqRight_2484_ = lean_ctor_get(v_toApplicative_2477_, 4);
v_isSharedCheck_2512_ = !lean_is_exclusive(v_toApplicative_2477_);
if (v_isSharedCheck_2512_ == 0)
{
lean_object* v_unused_2513_; 
v_unused_2513_ = lean_ctor_get(v_toApplicative_2477_, 1);
lean_dec(v_unused_2513_);
v___x_2486_ = v_toApplicative_2477_;
v_isShared_2487_ = v_isSharedCheck_2512_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_toSeqRight_2484_);
lean_inc(v_toSeqLeft_2483_);
lean_inc(v_toSeq_2482_);
lean_inc(v_toFunctor_2481_);
lean_dec(v_toApplicative_2477_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2512_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___f_2488_; lean_object* v___f_2489_; lean_object* v___f_2490_; lean_object* v___f_2491_; lean_object* v___x_2492_; lean_object* v___f_2493_; lean_object* v___f_2494_; lean_object* v___f_2495_; lean_object* v___x_2497_; 
v___f_2488_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__4));
v___f_2489_ = ((lean_object*)(l_Lean_Meta_Sym_instInhabitedSymM___closed__5));
lean_inc_ref(v_toFunctor_2481_);
v___f_2490_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2490_, 0, v_toFunctor_2481_);
v___f_2491_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2491_, 0, v_toFunctor_2481_);
v___x_2492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___f_2490_);
lean_ctor_set(v___x_2492_, 1, v___f_2491_);
v___f_2493_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2493_, 0, v_toSeqRight_2484_);
v___f_2494_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2494_, 0, v_toSeqLeft_2483_);
v___f_2495_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2495_, 0, v_toSeq_2482_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 4, v___f_2493_);
lean_ctor_set(v___x_2486_, 3, v___f_2494_);
lean_ctor_set(v___x_2486_, 2, v___f_2495_);
lean_ctor_set(v___x_2486_, 1, v___f_2488_);
lean_ctor_set(v___x_2486_, 0, v___x_2492_);
v___x_2497_ = v___x_2486_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2492_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v___f_2488_);
lean_ctor_set(v_reuseFailAlloc_2511_, 2, v___f_2495_);
lean_ctor_set(v_reuseFailAlloc_2511_, 3, v___f_2494_);
lean_ctor_set(v_reuseFailAlloc_2511_, 4, v___f_2493_);
v___x_2497_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
lean_object* v___x_2499_; 
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 1, v___f_2489_);
lean_ctor_set(v___x_2479_, 0, v___x_2497_);
v___x_2499_ = v___x_2479_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2497_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v___f_2489_);
v___x_2499_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v_toMonadRef_2504_; lean_object* v___f_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2500_ = l_StateRefT_x27_instMonad___redArg(v___x_2499_);
v___x_2501_ = l_ReaderT_instMonad___redArg(v___x_2500_);
v___x_2502_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__17, &l_Lean_Meta_Sym_instInhabitedSymM___closed__17_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__17);
v___x_2503_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__25, &l_Lean_Meta_Sym_instInhabitedSymM___closed__25_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__25);
v_toMonadRef_2504_ = lean_ctor_get(v___x_2503_, 0);
v___f_2505_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__27, &l_Lean_Meta_Sym_instInhabitedSymM___closed__27_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__27);
lean_inc_ref(v___x_2501_);
v___x_2506_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_2505_, v___x_2501_);
lean_inc_ref(v_toMonadRef_2504_);
v___x_2507_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2502_);
lean_ctor_set(v___x_2507_, 1, v_toMonadRef_2504_);
lean_ctor_set(v___x_2507_, 2, v___x_2506_);
v___x_2508_ = lean_obj_once(&l_Lean_Meta_Sym_instInhabitedSymM___closed__29, &l_Lean_Meta_Sym_instInhabitedSymM___closed__29_once, _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__29);
v___x_2509_ = l_Lean_throwError___redArg(v___x_2501_, v___x_2507_, v___x_2508_);
return v___x_2509_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(lean_object* v_ext_2516_, lean_object* v_extensions_2517_){
_start:
{
lean_object* v_id_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v_id_2519_ = lean_ctor_get(v_ext_2516_, 0);
v___x_2520_ = l_Lean_Meta_Sym_instInhabitedSymExtensionState;
v___x_2521_ = lean_array_get_borrowed(v___x_2520_, v_extensions_2517_, v_id_2519_);
lean_inc(v___x_2521_);
v___x_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg___boxed(lean_object* v_ext_2523_, lean_object* v_extensions_2524_, lean_object* v_a_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_2523_, v_extensions_2524_);
lean_dec_ref(v_extensions_2524_);
lean_dec_ref(v_ext_2523_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(lean_object* v_00_u03c3_2527_, lean_object* v_ext_2528_, lean_object* v_extensions_2529_){
_start:
{
lean_object* v___x_2531_; 
v___x_2531_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_2528_, v_extensions_2529_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___boxed(lean_object* v_00_u03c3_2532_, lean_object* v_ext_2533_, lean_object* v_extensions_2534_, lean_object* v_a_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(v_00_u03c3_2532_, v_ext_2533_, v_extensions_2534_);
lean_dec_ref(v_extensions_2534_);
lean_dec_ref(v_ext_2533_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg(lean_object* v_ext_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_){
_start:
{
lean_object* v___x_2541_; lean_object* v_extensions_2542_; lean_object* v___x_2543_; 
v___x_2541_ = lean_st_ref_get(v_a_2538_);
v_extensions_2542_ = lean_ctor_get(v___x_2541_, 7);
lean_inc_ref(v_extensions_2542_);
lean_dec(v___x_2541_);
v___x_2543_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_2537_, v_extensions_2542_);
lean_dec_ref(v_extensions_2542_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2543_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2543_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2564_; 
v_a_2552_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2554_ = v___x_2543_;
v_isShared_2555_ = v_isSharedCheck_2564_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2543_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2564_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v_ref_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2562_; 
v_ref_2556_ = lean_ctor_get(v_a_2539_, 5);
v___x_2557_ = lean_io_error_to_string(v_a_2552_);
v___x_2558_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
v___x_2559_ = l_Lean_MessageData_ofFormat(v___x_2558_);
lean_inc(v_ref_2556_);
v___x_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2560_, 0, v_ref_2556_);
lean_ctor_set(v___x_2560_, 1, v___x_2559_);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 0, v___x_2560_);
v___x_2562_ = v___x_2554_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2560_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg___boxed(lean_object* v_ext_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_2565_, v_a_2566_, v_a_2567_);
lean_dec_ref(v_a_2567_);
lean_dec(v_a_2566_);
lean_dec_ref(v_ext_2565_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState(lean_object* v_00_u03c3_2570_, lean_object* v_ext_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_){
_start:
{
lean_object* v___x_2579_; 
v___x_2579_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_2571_, v_a_2573_, v_a_2576_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SymExtension_getState___boxed(lean_object* v_00_u03c3_2580_, lean_object* v_ext_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Lean_Meta_Sym_SymExtension_getState(v_00_u03c3_2580_, v_ext_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
lean_dec(v_a_2585_);
lean_dec_ref(v_a_2584_);
lean_dec(v_a_2583_);
lean_dec_ref(v_a_2582_);
lean_dec_ref(v_ext_2581_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(lean_object* v_ext_2590_, lean_object* v_f_2591_, lean_object* v_a_2592_){
_start:
{
lean_object* v___x_2594_; lean_object* v_share_2595_; lean_object* v_maxFVar_2596_; lean_object* v_proofInstInfo_2597_; lean_object* v_inferType_2598_; lean_object* v_getLevel_2599_; lean_object* v_congrInfo_2600_; lean_object* v_defEqI_2601_; lean_object* v_extensions_2602_; lean_object* v_issues_2603_; lean_object* v_canon_2604_; uint8_t v_debug_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2624_; 
v___x_2594_ = lean_st_ref_take(v_a_2592_);
v_share_2595_ = lean_ctor_get(v___x_2594_, 0);
v_maxFVar_2596_ = lean_ctor_get(v___x_2594_, 1);
v_proofInstInfo_2597_ = lean_ctor_get(v___x_2594_, 2);
v_inferType_2598_ = lean_ctor_get(v___x_2594_, 3);
v_getLevel_2599_ = lean_ctor_get(v___x_2594_, 4);
v_congrInfo_2600_ = lean_ctor_get(v___x_2594_, 5);
v_defEqI_2601_ = lean_ctor_get(v___x_2594_, 6);
v_extensions_2602_ = lean_ctor_get(v___x_2594_, 7);
v_issues_2603_ = lean_ctor_get(v___x_2594_, 8);
v_canon_2604_ = lean_ctor_get(v___x_2594_, 9);
v_debug_2605_ = lean_ctor_get_uint8(v___x_2594_, sizeof(void*)*10);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2607_ = v___x_2594_;
v_isShared_2608_ = v_isSharedCheck_2624_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_canon_2604_);
lean_inc(v_issues_2603_);
lean_inc(v_extensions_2602_);
lean_inc(v_defEqI_2601_);
lean_inc(v_congrInfo_2600_);
lean_inc(v_getLevel_2599_);
lean_inc(v_inferType_2598_);
lean_inc(v_proofInstInfo_2597_);
lean_inc(v_maxFVar_2596_);
lean_inc(v_share_2595_);
lean_dec(v___x_2594_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2624_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v_id_2609_; lean_object* v___x_2610_; lean_object* v___y_2612_; lean_object* v___x_2618_; uint8_t v___x_2619_; 
v_id_2609_ = lean_ctor_get(v_ext_2590_, 0);
v___x_2610_ = lean_box(0);
v___x_2618_ = lean_array_get_size(v_extensions_2602_);
v___x_2619_ = lean_nat_dec_lt(v_id_2609_, v___x_2618_);
if (v___x_2619_ == 0)
{
lean_dec(v_f_2591_);
v___y_2612_ = v_extensions_2602_;
goto v___jp_2611_;
}
else
{
lean_object* v_v_2620_; lean_object* v_xs_x27_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v_v_2620_ = lean_array_fget(v_extensions_2602_, v_id_2609_);
v_xs_x27_2621_ = lean_array_fset(v_extensions_2602_, v_id_2609_, v___x_2610_);
v___x_2622_ = lean_apply_1(v_f_2591_, v_v_2620_);
v___x_2623_ = lean_array_fset(v_xs_x27_2621_, v_id_2609_, v___x_2622_);
v___y_2612_ = v___x_2623_;
goto v___jp_2611_;
}
v___jp_2611_:
{
lean_object* v___x_2614_; 
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 7, v___y_2612_);
v___x_2614_ = v___x_2607_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_share_2595_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v_maxFVar_2596_);
lean_ctor_set(v_reuseFailAlloc_2617_, 2, v_proofInstInfo_2597_);
lean_ctor_set(v_reuseFailAlloc_2617_, 3, v_inferType_2598_);
lean_ctor_set(v_reuseFailAlloc_2617_, 4, v_getLevel_2599_);
lean_ctor_set(v_reuseFailAlloc_2617_, 5, v_congrInfo_2600_);
lean_ctor_set(v_reuseFailAlloc_2617_, 6, v_defEqI_2601_);
lean_ctor_set(v_reuseFailAlloc_2617_, 7, v___y_2612_);
lean_ctor_set(v_reuseFailAlloc_2617_, 8, v_issues_2603_);
lean_ctor_set(v_reuseFailAlloc_2617_, 9, v_canon_2604_);
lean_ctor_set_uint8(v_reuseFailAlloc_2617_, sizeof(void*)*10, v_debug_2605_);
v___x_2614_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2615_ = lean_st_ref_set(v_a_2592_, v___x_2614_);
v___x_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2610_);
return v___x_2616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg___boxed(lean_object* v_ext_2625_, lean_object* v_f_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_2625_, v_f_2626_, v_a_2627_);
lean_dec(v_a_2627_);
lean_dec_ref(v_ext_2625_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(lean_object* v_00_u03c3_2630_, lean_object* v_ext_2631_, lean_object* v_f_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_){
_start:
{
lean_object* v___x_2640_; 
v___x_2640_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v_ext_2631_, v_f_2632_, v_a_2634_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___boxed(lean_object* v_00_u03c3_2641_, lean_object* v_ext_2642_, lean_object* v_f_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(v_00_u03c3_2641_, v_ext_2642_, v_f_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_);
lean_dec(v_a_2649_);
lean_dec_ref(v_a_2648_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
lean_dec_ref(v_ext_2642_);
return v_res_2651_;
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
