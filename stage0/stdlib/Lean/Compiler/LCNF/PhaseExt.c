// Lean compiler output
// Module: Lean.Compiler.LCNF.PhaseExt
// Imports: public import Lean.Compiler.LCNF.PassManager public import Lean.Compiler.LCNF.PublicDeclsExt
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_instInhabitedEnvExtension_default___redArg();
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited___redArg();
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_instInhabitedSignature_default___redArg();
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_Compiler_LCNF_isDeclPublic(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedDecl_default___redArg();
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3496178540____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3496178540____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_baseTransparentDeclsExt;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1977385844____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1977385844____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_monoTransparentDeclsExt;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_975450157____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_975450157____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_impureTransparentDeclsExt;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_getTransparencyExt(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_getTransparencyExt___boxed(lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_isDeclTransparent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_isDeclTransparent___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_isDeclTransparent___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isDeclTransparent(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isDeclTransparent___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setDeclTransparent___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setDeclTransparent(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setDeclTransparent___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__0_value;
static const lean_array_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "number of local entries: "};
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__1_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0;
static const lean_closure_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__2___closed__0_value),((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__2___closed__0_value),((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__4;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___redArg();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___boxed(lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4_value;
static const lean_array_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5_value;
static const lean_string_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7_value;
static const lean_string_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__8_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__9_value;
static const lean_string_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__10_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13;
static const lean_string_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__14 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__14_value;
static const lean_string_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__15 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__15_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16_value;
static const lean_string_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__17 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__17_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_mkDeclExt___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__2___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__3(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_mkDeclExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_mkDeclExt___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_mkDeclExt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_mkDeclExt___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_mkDeclExt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_mkDeclExt___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___closed__3;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___closed__4;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___closed__5;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "baseExt"};
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(145, 223, 165, 126, 7, 177, 183, 38)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_baseExt;
static const lean_string_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "monoExt"};
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 71, 195, 20, 53, 75, 103, 187)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_monoExt;
static const lean_closure_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___boxed, .m_arity = 6, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_impureExt;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__2___closed__0_value),((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__2___closed__0_value),((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___redArg();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedSigExt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0;
static const lean_closure_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___auto__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_mkSigDeclExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_mkSigDeclExt___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_mkSigDeclExt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_mkSigDeclExt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_mkSigDeclExt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__2_value)} };
static const lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__3_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "impureSigExt"};
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(245, 150, 154, 56, 193, 204, 147, 237)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_impureSigExt;
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclCore_x3f(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSigCore_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSigCore_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSigCore_x3f(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSigCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBaseDecl_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBaseDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__0_value;
static const lean_array_object l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecls___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecls___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecls(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecls___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveBaseDeclCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveMonoDeclCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveImpureDeclCore___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveImpureDeclCore(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveBase(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveMono(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_save___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_save___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_save___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_save___closed__1;
static const lean_closure_object l_Lean_Compiler_LCNF_Decl_save___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Decl_save___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_save___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Decl_save___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Decl_save___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_save___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "Internal compiler error: getDecl\? on impure is unsupported for now"};
static const lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDecl_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDecl_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_declOrderExt;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_recordFinalImpureDecl___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_recordFinalImpureDecl(lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__0 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__0_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__5 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__6 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__6_value;
static lean_once_cell_t l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__5(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Compiler.LCNF.PhaseExt"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Compiler.LCNF.getImpureDeclIndices"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "assertion violation: i != 0\n    "};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "assertion violation: map.size == targets.size\n  "};
static const lean_object* l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureDeclIndices(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureDeclIndices___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3496178540____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3496178540____hygCtx___hyg_2____boxed(lean_object* v_a_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3496178540____hygCtx___hyg_2_();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1977385844____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1977385844____hygCtx___hyg_2____boxed(lean_object* v_a_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1977385844____hygCtx___hyg_2_();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_975450157____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_975450157____hygCtx___hyg_2____boxed(lean_object* v_a_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_975450157____hygCtx___hyg_2_();
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_getTransparencyExt(uint8_t v_x_13_){
_start:
{
switch(v_x_13_)
{
case 0:
{
lean_object* v___x_14_; 
v___x_14_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_baseTransparentDeclsExt;
return v___x_14_;
}
case 1:
{
lean_object* v___x_15_; 
v___x_15_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_monoTransparentDeclsExt;
return v___x_15_;
}
default: 
{
lean_object* v___x_16_; 
v___x_16_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_impureTransparentDeclsExt;
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_getTransparencyExt___boxed(lean_object* v_x_17_){
_start:
{
uint8_t v_x_25__boxed_18_; lean_object* v_res_19_; 
v_x_25__boxed_18_ = lean_unbox(v_x_17_);
v_res_19_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_getTransparencyExt(v_x_25__boxed_18_);
return v_res_19_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isDeclTransparent(lean_object* v_env_23_, uint8_t v_phase_24_, lean_object* v_declName_25_){
_start:
{
lean_object* v___x_26_; uint8_t v_isModule_27_; 
v___x_26_ = l_Lean_Environment_header(v_env_23_);
v_isModule_27_ = lean_ctor_get_uint8(v___x_26_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_26_);
if (v_isModule_27_ == 0)
{
uint8_t v___x_28_; 
lean_dec_ref(v_env_23_);
v___x_28_ = 1;
return v___x_28_;
}
else
{
lean_object* v___x_29_; lean_object* v_asyncMode_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v_snd_34_; uint8_t v___x_35_; 
v___x_29_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_getTransparencyExt(v_phase_24_);
v_asyncMode_30_ = lean_ctor_get(v___x_29_, 2);
lean_inc(v_asyncMode_30_);
v___x_31_ = ((lean_object*)(l_Lean_Compiler_LCNF_isDeclTransparent___closed__0));
v___x_32_ = lean_box(0);
v___x_33_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_31_, v___x_29_, v_env_23_, v_asyncMode_30_, v___x_32_);
lean_dec(v_asyncMode_30_);
lean_dec_ref(v___x_29_);
v_snd_34_ = lean_ctor_get(v___x_33_, 1);
lean_inc(v_snd_34_);
lean_dec(v___x_33_);
v___x_35_ = l_Lean_NameSet_contains(v_snd_34_, v_declName_25_);
lean_dec(v_snd_34_);
return v___x_35_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isDeclTransparent___boxed(lean_object* v_env_36_, lean_object* v_phase_37_, lean_object* v_declName_38_){
_start:
{
uint8_t v_phase_boxed_39_; uint8_t v_res_40_; lean_object* v_r_41_; 
v_phase_boxed_39_ = lean_unbox(v_phase_37_);
v_res_40_ = l_Lean_Compiler_LCNF_isDeclTransparent(v_env_36_, v_phase_boxed_39_, v_declName_38_);
lean_dec(v_declName_38_);
v_r_41_ = lean_box(v_res_40_);
return v_r_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setDeclTransparent___lam__0(lean_object* v_declName_42_, lean_object* v_s_43_){
_start:
{
lean_object* v_fst_44_; lean_object* v_snd_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_54_; 
v_fst_44_ = lean_ctor_get(v_s_43_, 0);
v_snd_45_ = lean_ctor_get(v_s_43_, 1);
v_isSharedCheck_54_ = !lean_is_exclusive(v_s_43_);
if (v_isSharedCheck_54_ == 0)
{
v___x_47_ = v_s_43_;
v_isShared_48_ = v_isSharedCheck_54_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_snd_45_);
lean_inc(v_fst_44_);
lean_dec(v_s_43_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_54_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_52_; 
lean_inc(v_declName_42_);
v___x_49_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_49_, 0, v_declName_42_);
lean_ctor_set(v___x_49_, 1, v_fst_44_);
v___x_50_ = l_Lean_NameSet_insert(v_snd_45_, v_declName_42_);
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 1, v___x_50_);
lean_ctor_set(v___x_47_, 0, v___x_49_);
v___x_52_ = v___x_47_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_49_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v___x_50_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setDeclTransparent(lean_object* v_env_55_, uint8_t v_phase_56_, lean_object* v_declName_57_){
_start:
{
uint8_t v___x_58_; 
lean_inc_ref(v_env_55_);
v___x_58_ = l_Lean_Compiler_LCNF_isDeclTransparent(v_env_55_, v_phase_56_, v_declName_57_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; lean_object* v_asyncMode_60_; lean_object* v___f_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_59_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_getTransparencyExt(v_phase_56_);
v_asyncMode_60_ = lean_ctor_get(v___x_59_, 2);
lean_inc(v_asyncMode_60_);
v___f_61_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_setDeclTransparent___lam__0), 2, 1);
lean_closure_set(v___f_61_, 0, v_declName_57_);
v___x_62_ = lean_box(0);
v___x_63_ = l_Lean_EnvExtension_modifyState___redArg(v___x_59_, v_env_55_, v___f_61_, v_asyncMode_60_, v___x_62_);
lean_dec(v_asyncMode_60_);
return v___x_63_;
}
else
{
lean_dec(v_declName_57_);
return v_env_55_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setDeclTransparent___boxed(lean_object* v_env_64_, lean_object* v_phase_65_, lean_object* v_declName_66_){
_start:
{
uint8_t v_phase_boxed_67_; lean_object* v_res_68_; 
v_phase_boxed_67_ = lean_unbox(v_phase_65_);
v_res_68_ = l_Lean_Compiler_LCNF_setDeclTransparent(v_env_64_, v_phase_boxed_67_, v_declName_66_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___lam__0(lean_object* v_ps_69_, lean_object* v_x_70_, lean_object* v_v_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_array_push(v_ps_69_, v_v_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___lam__0___boxed(lean_object* v_ps_73_, lean_object* v_x_74_, lean_object* v_v_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___lam__0(v_ps_73_, v_x_74_, v_v_75_);
lean_dec(v_x_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_f_77_, lean_object* v_keys_78_, lean_object* v_vals_79_, lean_object* v_i_80_, lean_object* v_acc_81_){
_start:
{
lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_82_ = lean_array_get_size(v_keys_78_);
v___x_83_ = lean_nat_dec_lt(v_i_80_, v___x_82_);
if (v___x_83_ == 0)
{
lean_dec(v_i_80_);
lean_dec(v_f_77_);
return v_acc_81_;
}
else
{
lean_object* v_k_84_; lean_object* v_v_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v_k_84_ = lean_array_fget_borrowed(v_keys_78_, v_i_80_);
v_v_85_ = lean_array_fget_borrowed(v_vals_79_, v_i_80_);
lean_inc(v_f_77_);
lean_inc(v_v_85_);
lean_inc(v_k_84_);
v___x_86_ = lean_apply_3(v_f_77_, v_acc_81_, v_k_84_, v_v_85_);
v___x_87_ = lean_unsigned_to_nat(1u);
v___x_88_ = lean_nat_add(v_i_80_, v___x_87_);
lean_dec(v_i_80_);
v_i_80_ = v___x_88_;
v_acc_81_ = v___x_86_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_f_90_, lean_object* v_keys_91_, lean_object* v_vals_92_, lean_object* v_i_93_, lean_object* v_acc_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___redArg(v_f_90_, v_keys_91_, v_vals_92_, v_i_93_, v_acc_94_);
lean_dec_ref(v_vals_92_);
lean_dec_ref(v_keys_91_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_96_, lean_object* v_as_97_, size_t v_i_98_, size_t v_stop_99_, lean_object* v_b_100_){
_start:
{
lean_object* v___y_102_; uint8_t v___x_106_; 
v___x_106_ = lean_usize_dec_eq(v_i_98_, v_stop_99_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
v___x_107_ = lean_array_uget_borrowed(v_as_97_, v_i_98_);
switch(lean_obj_tag(v___x_107_))
{
case 0:
{
lean_object* v_key_108_; lean_object* v_val_109_; lean_object* v___x_110_; 
v_key_108_ = lean_ctor_get(v___x_107_, 0);
v_val_109_ = lean_ctor_get(v___x_107_, 1);
lean_inc(v_f_96_);
lean_inc(v_val_109_);
lean_inc(v_key_108_);
v___x_110_ = lean_apply_3(v_f_96_, v_b_100_, v_key_108_, v_val_109_);
v___y_102_ = v___x_110_;
goto v___jp_101_;
}
case 1:
{
lean_object* v_node_111_; lean_object* v___x_112_; 
v_node_111_ = lean_ctor_get(v___x_107_, 0);
lean_inc(v_f_96_);
v___x_112_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v_f_96_, v_node_111_, v_b_100_);
v___y_102_ = v___x_112_;
goto v___jp_101_;
}
default: 
{
v___y_102_ = v_b_100_;
goto v___jp_101_;
}
}
}
else
{
lean_dec(v_f_96_);
return v_b_100_;
}
v___jp_101_:
{
size_t v___x_103_; size_t v___x_104_; 
v___x_103_ = ((size_t)1ULL);
v___x_104_ = lean_usize_add(v_i_98_, v___x_103_);
v_i_98_ = v___x_104_;
v_b_100_ = v___y_102_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(lean_object* v_f_113_, lean_object* v_x_114_, lean_object* v_x_115_){
_start:
{
if (lean_obj_tag(v_x_114_) == 0)
{
lean_object* v_es_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v_es_116_ = lean_ctor_get(v_x_114_, 0);
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = lean_array_get_size(v_es_116_);
v___x_119_ = lean_nat_dec_lt(v___x_117_, v___x_118_);
if (v___x_119_ == 0)
{
lean_dec(v_f_113_);
return v_x_115_;
}
else
{
size_t v___x_120_; size_t v___x_121_; lean_object* v___x_122_; 
v___x_120_ = ((size_t)0ULL);
v___x_121_ = lean_usize_of_nat(v___x_118_);
v___x_122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg(v_f_113_, v_es_116_, v___x_120_, v___x_121_, v_x_115_);
return v___x_122_;
}
}
else
{
lean_object* v_ks_123_; lean_object* v_vs_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v_ks_123_ = lean_ctor_get(v_x_114_, 0);
v_vs_124_ = lean_ctor_get(v_x_114_, 1);
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___redArg(v_f_113_, v_ks_123_, v_vs_124_, v___x_125_, v_x_115_);
return v___x_126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_127_, lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v_f_127_, v_x_128_, v_x_129_);
lean_dec_ref(v_x_128_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_131_, lean_object* v_as_132_, lean_object* v_i_133_, lean_object* v_stop_134_, lean_object* v_b_135_){
_start:
{
size_t v_i_boxed_136_; size_t v_stop_boxed_137_; lean_object* v_res_138_; 
v_i_boxed_136_ = lean_unbox_usize(v_i_133_);
lean_dec(v_i_133_);
v_stop_boxed_137_ = lean_unbox_usize(v_stop_134_);
lean_dec(v_stop_134_);
v_res_138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg(v_f_131_, v_as_132_, v_i_boxed_136_, v_stop_boxed_137_, v_b_135_);
lean_dec_ref(v_as_132_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg___lam__0(lean_object* v_f_139_, lean_object* v_x1_140_, lean_object* v_x2_141_, lean_object* v_x3_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lean_apply_3(v_f_139_, v_x1_140_, v_x2_141_, v_x3_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(lean_object* v_map_144_, lean_object* v_f_145_, lean_object* v_init_146_){
_start:
{
lean_object* v___f_147_; lean_object* v___x_148_; 
v___f_147_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_147_, 0, v_f_145_);
v___x_148_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v___f_147_, v_map_144_, v_init_146_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg___boxed(lean_object* v_map_149_, lean_object* v_f_150_, lean_object* v_init_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_map_149_, v_f_150_, v_init_151_);
lean_dec_ref(v_map_149_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2___redArg(lean_object* v_lt_153_, lean_object* v_hi_154_, lean_object* v_pivot_155_, lean_object* v_as_156_, lean_object* v_i_157_, lean_object* v_k_158_){
_start:
{
uint8_t v___x_159_; 
v___x_159_ = lean_nat_dec_lt(v_k_158_, v_hi_154_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_dec(v_k_158_);
lean_dec(v_pivot_155_);
lean_dec_ref(v_lt_153_);
v___x_160_ = lean_array_fswap(v_as_156_, v_i_157_, v_hi_154_);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v_i_157_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
return v___x_161_;
}
else
{
lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_162_ = lean_array_fget_borrowed(v_as_156_, v_k_158_);
lean_inc_ref(v_lt_153_);
lean_inc(v_pivot_155_);
lean_inc(v___x_162_);
v___x_163_ = lean_apply_2(v_lt_153_, v___x_162_, v_pivot_155_);
v___x_164_ = lean_unbox(v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = lean_nat_add(v_k_158_, v___x_165_);
lean_dec(v_k_158_);
v_k_158_ = v___x_166_;
goto _start;
}
else
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_168_ = lean_array_fswap(v_as_156_, v_i_157_, v_k_158_);
v___x_169_ = lean_unsigned_to_nat(1u);
v___x_170_ = lean_nat_add(v_i_157_, v___x_169_);
lean_dec(v_i_157_);
v___x_171_ = lean_nat_add(v_k_158_, v___x_169_);
lean_dec(v_k_158_);
v_as_156_ = v___x_168_;
v_i_157_ = v___x_170_;
v_k_158_ = v___x_171_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2___redArg___boxed(lean_object* v_lt_173_, lean_object* v_hi_174_, lean_object* v_pivot_175_, lean_object* v_as_176_, lean_object* v_i_177_, lean_object* v_k_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2___redArg(v_lt_173_, v_hi_174_, v_pivot_175_, v_as_176_, v_i_177_, v_k_178_);
lean_dec(v_hi_174_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(lean_object* v_lt_180_, lean_object* v_n_181_, lean_object* v_as_182_, lean_object* v_lo_183_, lean_object* v_hi_184_){
_start:
{
lean_object* v___y_186_; uint8_t v___x_196_; 
v___x_196_ = lean_nat_dec_lt(v_lo_183_, v_hi_184_);
if (v___x_196_ == 0)
{
lean_dec(v_lo_183_);
lean_dec_ref(v_lt_180_);
return v_as_182_;
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v_mid_199_; lean_object* v___y_201_; lean_object* v___y_208_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_197_ = lean_nat_add(v_lo_183_, v_hi_184_);
v___x_198_ = lean_unsigned_to_nat(1u);
v_mid_199_ = lean_nat_shiftr(v___x_197_, v___x_198_);
lean_dec(v___x_197_);
v___x_214_ = lean_array_fget_borrowed(v_as_182_, v_mid_199_);
v___x_215_ = lean_array_fget_borrowed(v_as_182_, v_lo_183_);
lean_inc_ref(v_lt_180_);
lean_inc(v___x_215_);
lean_inc(v___x_214_);
v___x_216_ = lean_apply_2(v_lt_180_, v___x_214_, v___x_215_);
v___x_217_ = lean_unbox(v___x_216_);
if (v___x_217_ == 0)
{
v___y_208_ = v_as_182_;
goto v___jp_207_;
}
else
{
lean_object* v___x_218_; 
v___x_218_ = lean_array_fswap(v_as_182_, v_lo_183_, v_mid_199_);
v___y_208_ = v___x_218_;
goto v___jp_207_;
}
v___jp_200_:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_202_ = lean_array_fget_borrowed(v___y_201_, v_mid_199_);
v___x_203_ = lean_array_fget_borrowed(v___y_201_, v_hi_184_);
lean_inc_ref(v_lt_180_);
lean_inc(v___x_203_);
lean_inc(v___x_202_);
v___x_204_ = lean_apply_2(v_lt_180_, v___x_202_, v___x_203_);
v___x_205_ = lean_unbox(v___x_204_);
if (v___x_205_ == 0)
{
lean_dec(v_mid_199_);
v___y_186_ = v___y_201_;
goto v___jp_185_;
}
else
{
lean_object* v___x_206_; 
v___x_206_ = lean_array_fswap(v___y_201_, v_mid_199_, v_hi_184_);
lean_dec(v_mid_199_);
v___y_186_ = v___x_206_;
goto v___jp_185_;
}
}
v___jp_207_:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_209_ = lean_array_fget_borrowed(v___y_208_, v_hi_184_);
v___x_210_ = lean_array_fget_borrowed(v___y_208_, v_lo_183_);
lean_inc_ref(v_lt_180_);
lean_inc(v___x_210_);
lean_inc(v___x_209_);
v___x_211_ = lean_apply_2(v_lt_180_, v___x_209_, v___x_210_);
v___x_212_ = lean_unbox(v___x_211_);
if (v___x_212_ == 0)
{
v___y_201_ = v___y_208_;
goto v___jp_200_;
}
else
{
lean_object* v___x_213_; 
v___x_213_ = lean_array_fswap(v___y_208_, v_lo_183_, v_hi_184_);
v___y_201_ = v___x_213_;
goto v___jp_200_;
}
}
}
v___jp_185_:
{
lean_object* v_pivot_187_; lean_object* v___x_188_; lean_object* v_fst_189_; lean_object* v_snd_190_; uint8_t v___x_191_; 
v_pivot_187_ = lean_array_fget(v___y_186_, v_hi_184_);
lean_inc_n(v_lo_183_, 2);
lean_inc_ref(v_lt_180_);
v___x_188_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2___redArg(v_lt_180_, v_hi_184_, v_pivot_187_, v___y_186_, v_lo_183_, v_lo_183_);
v_fst_189_ = lean_ctor_get(v___x_188_, 0);
lean_inc(v_fst_189_);
v_snd_190_ = lean_ctor_get(v___x_188_, 1);
lean_inc(v_snd_190_);
lean_dec_ref(v___x_188_);
v___x_191_ = lean_nat_dec_le(v_hi_184_, v_fst_189_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
lean_inc_ref(v_lt_180_);
v___x_192_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_180_, v_n_181_, v_snd_190_, v_lo_183_, v_fst_189_);
v___x_193_ = lean_unsigned_to_nat(1u);
v___x_194_ = lean_nat_add(v_fst_189_, v___x_193_);
lean_dec(v_fst_189_);
v_as_182_ = v___x_192_;
v_lo_183_ = v___x_194_;
goto _start;
}
else
{
lean_dec(v_fst_189_);
lean_dec(v_lo_183_);
lean_dec_ref(v_lt_180_);
return v_snd_190_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg___boxed(lean_object* v_lt_219_, lean_object* v_n_220_, lean_object* v_as_221_, lean_object* v_lo_222_, lean_object* v_hi_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_219_, v_n_220_, v_as_221_, v_lo_222_, v_hi_223_);
lean_dec(v_hi_223_);
lean_dec(v_n_220_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(lean_object* v_s_228_, lean_object* v_lt_229_){
_start:
{
lean_object* v___f_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v_decls_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v___f_230_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__0));
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__1));
v_decls_233_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_s_228_, v___f_230_, v___x_232_);
v___x_234_ = lean_array_get_size(v_decls_233_);
v___x_235_ = lean_nat_dec_eq(v___x_234_, v___x_231_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___y_239_; uint8_t v___x_243_; 
v___x_236_ = lean_unsigned_to_nat(1u);
v___x_237_ = lean_nat_sub(v___x_234_, v___x_236_);
v___x_243_ = lean_nat_dec_le(v___x_231_, v___x_237_);
if (v___x_243_ == 0)
{
lean_inc(v___x_237_);
v___y_239_ = v___x_237_;
goto v___jp_238_;
}
else
{
v___y_239_ = v___x_231_;
goto v___jp_238_;
}
v___jp_238_:
{
uint8_t v___x_240_; 
v___x_240_ = lean_nat_dec_le(v___y_239_, v___x_237_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; 
lean_dec(v___x_237_);
lean_inc(v___y_239_);
v___x_241_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_229_, v___x_234_, v_decls_233_, v___y_239_, v___y_239_);
lean_dec(v___y_239_);
return v___x_241_;
}
else
{
lean_object* v___x_242_; 
v___x_242_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_229_, v___x_234_, v_decls_233_, v___y_239_, v___x_237_);
lean_dec(v___x_237_);
return v___x_242_;
}
}
}
else
{
lean_dec_ref(v_lt_229_);
return v_decls_233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___boxed(lean_object* v_s_244_, lean_object* v_lt_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(v_s_244_, v_lt_245_);
lean_dec_ref(v_s_244_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries(uint8_t v_pu_247_, lean_object* v_00_u03b2_248_, lean_object* v_s_249_, lean_object* v_lt_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(v_s_249_, v_lt_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___boxed(lean_object* v_pu_252_, lean_object* v_00_u03b2_253_, lean_object* v_s_254_, lean_object* v_lt_255_){
_start:
{
uint8_t v_pu_boxed_256_; lean_object* v_res_257_; 
v_pu_boxed_256_ = lean_unbox(v_pu_252_);
v_res_257_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries(v_pu_boxed_256_, v_00_u03b2_253_, v_s_254_, v_lt_255_);
lean_dec_ref(v_s_254_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0(lean_object* v_00_u03c3_258_, lean_object* v_00_u03b2_259_, lean_object* v_map_260_, lean_object* v_f_261_, lean_object* v_init_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_map_260_, v_f_261_, v_init_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___boxed(lean_object* v_00_u03c3_264_, lean_object* v_00_u03b2_265_, lean_object* v_map_266_, lean_object* v_f_267_, lean_object* v_init_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0(v_00_u03c3_264_, v_00_u03b2_265_, v_map_266_, v_f_267_, v_init_268_);
lean_dec_ref(v_map_266_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1(lean_object* v_00_u03b2_270_, lean_object* v_lt_271_, lean_object* v_n_272_, lean_object* v_as_273_, lean_object* v_lo_274_, lean_object* v_hi_275_, lean_object* v_w_276_, lean_object* v_hlo_277_, lean_object* v_hhi_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_271_, v_n_272_, v_as_273_, v_lo_274_, v_hi_275_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___boxed(lean_object* v_00_u03b2_280_, lean_object* v_lt_281_, lean_object* v_n_282_, lean_object* v_as_283_, lean_object* v_lo_284_, lean_object* v_hi_285_, lean_object* v_w_286_, lean_object* v_hlo_287_, lean_object* v_hhi_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1(v_00_u03b2_280_, v_lt_281_, v_n_282_, v_as_283_, v_lo_284_, v_hi_285_, v_w_286_, v_hlo_287_, v_hhi_288_);
lean_dec(v_hi_285_);
lean_dec(v_n_282_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___redArg(lean_object* v_map_290_, lean_object* v_f_291_, lean_object* v_init_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v_f_291_, v_map_290_, v_init_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___redArg___boxed(lean_object* v_map_294_, lean_object* v_f_295_, lean_object* v_init_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___redArg(v_map_294_, v_f_295_, v_init_296_);
lean_dec_ref(v_map_294_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0(lean_object* v_00_u03c3_298_, lean_object* v_00_u03b2_299_, lean_object* v_map_300_, lean_object* v_f_301_, lean_object* v_init_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v_f_301_, v_map_300_, v_init_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___boxed(lean_object* v_00_u03c3_304_, lean_object* v_00_u03b2_305_, lean_object* v_map_306_, lean_object* v_f_307_, lean_object* v_init_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0(v_00_u03c3_304_, v_00_u03b2_305_, v_map_306_, v_f_307_, v_init_308_);
lean_dec_ref(v_map_306_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2(lean_object* v_00_u03b2_310_, lean_object* v_lt_311_, lean_object* v_n_312_, lean_object* v_lo_313_, lean_object* v_hi_314_, lean_object* v_hhi_315_, lean_object* v_pivot_316_, lean_object* v_as_317_, lean_object* v_i_318_, lean_object* v_k_319_, lean_object* v_ilo_320_, lean_object* v_ik_321_, lean_object* v_w_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2___redArg(v_lt_311_, v_hi_314_, v_pivot_316_, v_as_317_, v_i_318_, v_k_319_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2___boxed(lean_object* v_00_u03b2_324_, lean_object* v_lt_325_, lean_object* v_n_326_, lean_object* v_lo_327_, lean_object* v_hi_328_, lean_object* v_hhi_329_, lean_object* v_pivot_330_, lean_object* v_as_331_, lean_object* v_i_332_, lean_object* v_k_333_, lean_object* v_ilo_334_, lean_object* v_ik_335_, lean_object* v_w_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2(v_00_u03b2_324_, v_lt_325_, v_n_326_, v_lo_327_, v_hi_328_, v_hhi_329_, v_pivot_330_, v_as_331_, v_i_332_, v_k_333_, v_ilo_334_, v_ik_335_, v_w_336_);
lean_dec(v_hi_328_);
lean_dec(v_lo_327_);
lean_dec(v_n_326_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_338_, lean_object* v_00_u03b1_339_, lean_object* v_00_u03b2_340_, lean_object* v_f_341_, lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v_f_341_, v_x_342_, v_x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_345_, lean_object* v_00_u03b1_346_, lean_object* v_00_u03b2_347_, lean_object* v_f_348_, lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1(v_00_u03c3_345_, v_00_u03b1_346_, v_00_u03b2_347_, v_f_348_, v_x_349_, v_x_350_);
lean_dec_ref(v_x_349_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_352_, lean_object* v_00_u03b2_353_, lean_object* v_00_u03c3_354_, lean_object* v_f_355_, lean_object* v_as_356_, size_t v_i_357_, size_t v_stop_358_, lean_object* v_b_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg(v_f_355_, v_as_356_, v_i_357_, v_stop_358_, v_b_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_361_, lean_object* v_00_u03b2_362_, lean_object* v_00_u03c3_363_, lean_object* v_f_364_, lean_object* v_as_365_, lean_object* v_i_366_, lean_object* v_stop_367_, lean_object* v_b_368_){
_start:
{
size_t v_i_boxed_369_; size_t v_stop_boxed_370_; lean_object* v_res_371_; 
v_i_boxed_369_ = lean_unbox_usize(v_i_366_);
lean_dec(v_i_366_);
v_stop_boxed_370_ = lean_unbox_usize(v_stop_367_);
lean_dec(v_stop_367_);
v_res_371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_361_, v_00_u03b2_362_, v_00_u03c3_363_, v_f_364_, v_as_365_, v_i_boxed_369_, v_stop_boxed_370_, v_b_368_);
lean_dec_ref(v_as_365_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03c3_372_, lean_object* v_00_u03b1_373_, lean_object* v_00_u03b2_374_, lean_object* v_f_375_, lean_object* v_keys_376_, lean_object* v_vals_377_, lean_object* v_heq_378_, lean_object* v_i_379_, lean_object* v_acc_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___redArg(v_f_375_, v_keys_376_, v_vals_377_, v_i_379_, v_acc_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03c3_382_, lean_object* v_00_u03b1_383_, lean_object* v_00_u03b2_384_, lean_object* v_f_385_, lean_object* v_keys_386_, lean_object* v_vals_387_, lean_object* v_heq_388_, lean_object* v_i_389_, lean_object* v_acc_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4(v_00_u03c3_382_, v_00_u03b1_383_, v_00_u03b2_384_, v_f_385_, v_keys_386_, v_vals_387_, v_heq_388_, v_i_389_, v_acc_390_);
lean_dec_ref(v_vals_387_);
lean_dec_ref(v_keys_386_);
return v_res_391_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_392_, lean_object* v_i_393_, lean_object* v_k_394_){
_start:
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = lean_array_get_size(v_keys_392_);
v___x_396_ = lean_nat_dec_lt(v_i_393_, v___x_395_);
if (v___x_396_ == 0)
{
lean_dec(v_i_393_);
return v___x_396_;
}
else
{
lean_object* v_k_x27_397_; uint8_t v___x_398_; 
v_k_x27_397_ = lean_array_fget_borrowed(v_keys_392_, v_i_393_);
v___x_398_ = lean_name_eq(v_k_394_, v_k_x27_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = lean_unsigned_to_nat(1u);
v___x_400_ = lean_nat_add(v_i_393_, v___x_399_);
lean_dec(v_i_393_);
v_i_393_ = v___x_400_;
goto _start;
}
else
{
lean_dec(v_i_393_);
return v___x_396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_402_, lean_object* v_i_403_, lean_object* v_k_404_){
_start:
{
uint8_t v_res_405_; lean_object* v_r_406_; 
v_res_405_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg(v_keys_402_, v_i_403_, v_k_404_);
lean_dec(v_k_404_);
lean_dec_ref(v_keys_402_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg(lean_object* v_x_407_, size_t v_x_408_, lean_object* v_x_409_){
_start:
{
if (lean_obj_tag(v_x_407_) == 0)
{
lean_object* v_es_410_; lean_object* v___x_411_; size_t v___x_412_; size_t v___x_413_; lean_object* v_j_414_; lean_object* v___x_415_; 
v_es_410_ = lean_ctor_get(v_x_407_, 0);
v___x_411_ = lean_box(2);
v___x_412_ = ((size_t)31ULL);
v___x_413_ = lean_usize_land(v_x_408_, v___x_412_);
v_j_414_ = lean_usize_to_nat(v___x_413_);
v___x_415_ = lean_array_get_borrowed(v___x_411_, v_es_410_, v_j_414_);
lean_dec(v_j_414_);
switch(lean_obj_tag(v___x_415_))
{
case 0:
{
lean_object* v_key_416_; uint8_t v___x_417_; 
v_key_416_ = lean_ctor_get(v___x_415_, 0);
v___x_417_ = lean_name_eq(v_x_409_, v_key_416_);
return v___x_417_;
}
case 1:
{
lean_object* v_node_418_; size_t v___x_419_; size_t v___x_420_; 
v_node_418_ = lean_ctor_get(v___x_415_, 0);
v___x_419_ = ((size_t)5ULL);
v___x_420_ = lean_usize_shift_right(v_x_408_, v___x_419_);
v_x_407_ = v_node_418_;
v_x_408_ = v___x_420_;
goto _start;
}
default: 
{
uint8_t v___x_422_; 
v___x_422_ = 0;
return v___x_422_;
}
}
}
else
{
lean_object* v_ks_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v_ks_423_ = lean_ctor_get(v_x_407_, 0);
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg(v_ks_423_, v___x_424_, v_x_409_);
return v___x_425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___boxed(lean_object* v_x_426_, lean_object* v_x_427_, lean_object* v_x_428_){
_start:
{
size_t v_x_410__boxed_429_; uint8_t v_res_430_; lean_object* v_r_431_; 
v_x_410__boxed_429_ = lean_unbox_usize(v_x_427_);
lean_dec(v_x_427_);
v_res_430_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg(v_x_426_, v_x_410__boxed_429_, v_x_428_);
lean_dec(v_x_428_);
lean_dec_ref(v_x_426_);
v_r_431_ = lean_box(v_res_430_);
return v_r_431_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg(lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
uint64_t v___y_435_; 
if (lean_obj_tag(v_x_433_) == 0)
{
uint64_t v___x_438_; 
v___x_438_ = 1723ULL;
v___y_435_ = v___x_438_;
goto v___jp_434_;
}
else
{
uint64_t v_hash_439_; 
v_hash_439_ = lean_ctor_get_uint64(v_x_433_, sizeof(void*)*2);
v___y_435_ = v_hash_439_;
goto v___jp_434_;
}
v___jp_434_:
{
size_t v___x_436_; uint8_t v___x_437_; 
v___x_436_ = lean_uint64_to_usize(v___y_435_);
v___x_437_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg(v_x_432_, v___x_436_, v_x_433_);
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___boxed(lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
uint8_t v_res_442_; lean_object* v_r_443_; 
v_res_442_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg(v_x_440_, v_x_441_);
lean_dec(v_x_441_);
lean_dec_ref(v_x_440_);
v_r_443_ = lean_box(v_res_442_);
return v_r_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_444_, lean_object* v_x_445_, lean_object* v_x_446_, lean_object* v_x_447_){
_start:
{
lean_object* v_ks_448_; lean_object* v_vs_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_473_; 
v_ks_448_ = lean_ctor_get(v_x_444_, 0);
v_vs_449_ = lean_ctor_get(v_x_444_, 1);
v_isSharedCheck_473_ = !lean_is_exclusive(v_x_444_);
if (v_isSharedCheck_473_ == 0)
{
v___x_451_ = v_x_444_;
v_isShared_452_ = v_isSharedCheck_473_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_vs_449_);
lean_inc(v_ks_448_);
lean_dec(v_x_444_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_473_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = lean_array_get_size(v_ks_448_);
v___x_454_ = lean_nat_dec_lt(v_x_445_, v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
lean_dec(v_x_445_);
v___x_455_ = lean_array_push(v_ks_448_, v_x_446_);
v___x_456_ = lean_array_push(v_vs_449_, v_x_447_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v___x_456_);
lean_ctor_set(v___x_451_, 0, v___x_455_);
v___x_458_ = v___x_451_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_455_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
else
{
lean_object* v_k_x27_460_; uint8_t v___x_461_; 
v_k_x27_460_ = lean_array_fget_borrowed(v_ks_448_, v_x_445_);
v___x_461_ = lean_name_eq(v_x_446_, v_k_x27_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_463_; 
if (v_isShared_452_ == 0)
{
v___x_463_ = v___x_451_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_ks_448_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_vs_449_);
v___x_463_ = v_reuseFailAlloc_467_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_unsigned_to_nat(1u);
v___x_465_ = lean_nat_add(v_x_445_, v___x_464_);
lean_dec(v_x_445_);
v_x_444_ = v___x_463_;
v_x_445_ = v___x_465_;
goto _start;
}
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_468_ = lean_array_fset(v_ks_448_, v_x_445_, v_x_446_);
v___x_469_ = lean_array_fset(v_vs_449_, v_x_445_, v_x_447_);
lean_dec(v_x_445_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v___x_469_);
lean_ctor_set(v___x_451_, 0, v___x_468_);
v___x_471_ = v___x_451_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v___x_469_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4___redArg(lean_object* v_n_474_, lean_object* v_k_475_, lean_object* v_v_476_){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_unsigned_to_nat(0u);
v___x_478_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4_spec__5___redArg(v_n_474_, v___x_477_, v_k_475_, v_v_476_);
return v___x_478_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(lean_object* v_x_480_, size_t v_x_481_, size_t v_x_482_, lean_object* v_x_483_, lean_object* v_x_484_){
_start:
{
if (lean_obj_tag(v_x_480_) == 0)
{
lean_object* v_es_485_; size_t v___x_486_; size_t v___x_487_; lean_object* v_j_488_; lean_object* v___x_489_; uint8_t v___x_490_; 
v_es_485_ = lean_ctor_get(v_x_480_, 0);
v___x_486_ = ((size_t)31ULL);
v___x_487_ = lean_usize_land(v_x_481_, v___x_486_);
v_j_488_ = lean_usize_to_nat(v___x_487_);
v___x_489_ = lean_array_get_size(v_es_485_);
v___x_490_ = lean_nat_dec_lt(v_j_488_, v___x_489_);
if (v___x_490_ == 0)
{
lean_dec(v_j_488_);
lean_dec(v_x_484_);
lean_dec(v_x_483_);
return v_x_480_;
}
else
{
lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_529_; 
lean_inc_ref(v_es_485_);
v_isSharedCheck_529_ = !lean_is_exclusive(v_x_480_);
if (v_isSharedCheck_529_ == 0)
{
lean_object* v_unused_530_; 
v_unused_530_ = lean_ctor_get(v_x_480_, 0);
lean_dec(v_unused_530_);
v___x_492_ = v_x_480_;
v_isShared_493_ = v_isSharedCheck_529_;
goto v_resetjp_491_;
}
else
{
lean_dec(v_x_480_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_529_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v_v_494_; lean_object* v___x_495_; lean_object* v_xs_x27_496_; lean_object* v___y_498_; 
v_v_494_ = lean_array_fget(v_es_485_, v_j_488_);
v___x_495_ = lean_box(0);
v_xs_x27_496_ = lean_array_fset(v_es_485_, v_j_488_, v___x_495_);
switch(lean_obj_tag(v_v_494_))
{
case 0:
{
lean_object* v_key_503_; lean_object* v_val_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_514_; 
v_key_503_ = lean_ctor_get(v_v_494_, 0);
v_val_504_ = lean_ctor_get(v_v_494_, 1);
v_isSharedCheck_514_ = !lean_is_exclusive(v_v_494_);
if (v_isSharedCheck_514_ == 0)
{
v___x_506_ = v_v_494_;
v_isShared_507_ = v_isSharedCheck_514_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_val_504_);
lean_inc(v_key_503_);
lean_dec(v_v_494_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_514_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
uint8_t v___x_508_; 
v___x_508_ = lean_name_eq(v_x_483_, v_key_503_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; lean_object* v___x_510_; 
lean_del_object(v___x_506_);
v___x_509_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_503_, v_val_504_, v_x_483_, v_x_484_);
v___x_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
v___y_498_ = v___x_510_;
goto v___jp_497_;
}
else
{
lean_object* v___x_512_; 
lean_dec(v_val_504_);
lean_dec(v_key_503_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 1, v_x_484_);
lean_ctor_set(v___x_506_, 0, v_x_483_);
v___x_512_ = v___x_506_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_x_483_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_x_484_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
v___y_498_ = v___x_512_;
goto v___jp_497_;
}
}
}
}
case 1:
{
lean_object* v_node_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_527_; 
v_node_515_ = lean_ctor_get(v_v_494_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v_v_494_);
if (v_isSharedCheck_527_ == 0)
{
v___x_517_ = v_v_494_;
v_isShared_518_ = v_isSharedCheck_527_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_node_515_);
lean_dec(v_v_494_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_527_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
size_t v___x_519_; size_t v___x_520_; size_t v___x_521_; size_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_519_ = ((size_t)5ULL);
v___x_520_ = lean_usize_shift_right(v_x_481_, v___x_519_);
v___x_521_ = ((size_t)1ULL);
v___x_522_ = lean_usize_add(v_x_482_, v___x_521_);
v___x_523_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_node_515_, v___x_520_, v___x_522_, v_x_483_, v_x_484_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_523_);
v___x_525_ = v___x_517_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
v___y_498_ = v___x_525_;
goto v___jp_497_;
}
}
}
default: 
{
lean_object* v___x_528_; 
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v_x_483_);
lean_ctor_set(v___x_528_, 1, v_x_484_);
v___y_498_ = v___x_528_;
goto v___jp_497_;
}
}
v___jp_497_:
{
lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_499_ = lean_array_fset(v_xs_x27_496_, v_j_488_, v___y_498_);
lean_dec(v_j_488_);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v___x_499_);
v___x_501_ = v___x_492_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
else
{
lean_object* v_ks_531_; lean_object* v_vs_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_550_; 
v_ks_531_ = lean_ctor_get(v_x_480_, 0);
v_vs_532_ = lean_ctor_get(v_x_480_, 1);
v_isSharedCheck_550_ = !lean_is_exclusive(v_x_480_);
if (v_isSharedCheck_550_ == 0)
{
v___x_534_ = v_x_480_;
v_isShared_535_ = v_isSharedCheck_550_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_vs_532_);
lean_inc(v_ks_531_);
lean_dec(v_x_480_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_550_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_ks_531_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_vs_532_);
v___x_537_ = v_reuseFailAlloc_549_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v_newNode_538_; size_t v___x_539_; uint8_t v___x_540_; 
v_newNode_538_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4___redArg(v___x_537_, v_x_483_, v_x_484_);
v___x_539_ = ((size_t)7ULL);
v___x_540_ = lean_usize_dec_le(v___x_539_, v_x_482_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_541_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_538_);
v___x_542_ = lean_unsigned_to_nat(4u);
v___x_543_ = lean_nat_dec_lt(v___x_541_, v___x_542_);
lean_dec(v___x_541_);
if (v___x_543_ == 0)
{
lean_object* v_ks_544_; lean_object* v_vs_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v_ks_544_ = lean_ctor_get(v_newNode_538_, 0);
lean_inc_ref(v_ks_544_);
v_vs_545_ = lean_ctor_get(v_newNode_538_, 1);
lean_inc_ref(v_vs_545_);
lean_dec_ref(v_newNode_538_);
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0);
v___x_548_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg(v_x_482_, v_ks_544_, v_vs_545_, v___x_546_, v___x_547_);
lean_dec_ref(v_vs_545_);
lean_dec_ref(v_ks_544_);
return v___x_548_;
}
else
{
return v_newNode_538_;
}
}
else
{
return v_newNode_538_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg(size_t v_depth_551_, lean_object* v_keys_552_, lean_object* v_vals_553_, lean_object* v_i_554_, lean_object* v_entries_555_){
_start:
{
lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_556_ = lean_array_get_size(v_keys_552_);
v___x_557_ = lean_nat_dec_lt(v_i_554_, v___x_556_);
if (v___x_557_ == 0)
{
lean_dec(v_i_554_);
return v_entries_555_;
}
else
{
lean_object* v_k_558_; lean_object* v_v_559_; uint64_t v___y_561_; 
v_k_558_ = lean_array_fget_borrowed(v_keys_552_, v_i_554_);
v_v_559_ = lean_array_fget_borrowed(v_vals_553_, v_i_554_);
if (lean_obj_tag(v_k_558_) == 0)
{
uint64_t v___x_572_; 
v___x_572_ = 1723ULL;
v___y_561_ = v___x_572_;
goto v___jp_560_;
}
else
{
uint64_t v_hash_573_; 
v_hash_573_ = lean_ctor_get_uint64(v_k_558_, sizeof(void*)*2);
v___y_561_ = v_hash_573_;
goto v___jp_560_;
}
v___jp_560_:
{
size_t v_h_562_; size_t v___x_563_; lean_object* v___x_564_; size_t v___x_565_; size_t v___x_566_; size_t v___x_567_; size_t v_h_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v_h_562_ = lean_uint64_to_usize(v___y_561_);
v___x_563_ = ((size_t)5ULL);
v___x_564_ = lean_unsigned_to_nat(1u);
v___x_565_ = ((size_t)1ULL);
v___x_566_ = lean_usize_sub(v_depth_551_, v___x_565_);
v___x_567_ = lean_usize_mul(v___x_563_, v___x_566_);
v_h_568_ = lean_usize_shift_right(v_h_562_, v___x_567_);
v___x_569_ = lean_nat_add(v_i_554_, v___x_564_);
lean_dec(v_i_554_);
lean_inc(v_v_559_);
lean_inc(v_k_558_);
v___x_570_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_entries_555_, v_h_568_, v_depth_551_, v_k_558_, v_v_559_);
v_i_554_ = v___x_569_;
v_entries_555_ = v___x_570_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_574_, lean_object* v_keys_575_, lean_object* v_vals_576_, lean_object* v_i_577_, lean_object* v_entries_578_){
_start:
{
size_t v_depth_boxed_579_; lean_object* v_res_580_; 
v_depth_boxed_579_ = lean_unbox_usize(v_depth_574_);
lean_dec(v_depth_574_);
v_res_580_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg(v_depth_boxed_579_, v_keys_575_, v_vals_576_, v_i_577_, v_entries_578_);
lean_dec_ref(v_vals_576_);
lean_dec_ref(v_keys_575_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___boxed(lean_object* v_x_581_, lean_object* v_x_582_, lean_object* v_x_583_, lean_object* v_x_584_, lean_object* v_x_585_){
_start:
{
size_t v_x_545__boxed_586_; size_t v_x_546__boxed_587_; lean_object* v_res_588_; 
v_x_545__boxed_586_ = lean_unbox_usize(v_x_582_);
lean_dec(v_x_582_);
v_x_546__boxed_587_ = lean_unbox_usize(v_x_583_);
lean_dec(v_x_583_);
v_res_588_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_x_581_, v_x_545__boxed_586_, v_x_546__boxed_587_, v_x_584_, v_x_585_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(lean_object* v_x_589_, lean_object* v_x_590_, lean_object* v_x_591_){
_start:
{
uint64_t v___y_593_; 
if (lean_obj_tag(v_x_590_) == 0)
{
uint64_t v___x_597_; 
v___x_597_ = 1723ULL;
v___y_593_ = v___x_597_;
goto v___jp_592_;
}
else
{
uint64_t v_hash_598_; 
v_hash_598_ = lean_ctor_get_uint64(v_x_590_, sizeof(void*)*2);
v___y_593_ = v_hash_598_;
goto v___jp_592_;
}
v___jp_592_:
{
size_t v___x_594_; size_t v___x_595_; lean_object* v___x_596_; 
v___x_594_ = lean_uint64_to_usize(v___y_593_);
v___x_595_ = ((size_t)1ULL);
v___x_596_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_x_589_, v___x_594_, v___x_595_, v_x_590_, v_x_591_);
return v___x_596_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___lam__0(lean_object* v_oldState_599_, lean_object* v_otherState_600_, lean_object* v_k_601_, lean_object* v_v_602_){
_start:
{
uint8_t v___x_603_; 
v___x_603_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg(v_oldState_599_, v_k_601_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_otherState_600_, v_k_601_, v_v_602_);
return v___x_604_;
}
else
{
lean_dec(v_v_602_);
lean_dec(v_k_601_);
return v_otherState_600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___lam__0___boxed(lean_object* v_oldState_605_, lean_object* v_otherState_606_, lean_object* v_k_607_, lean_object* v_v_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___lam__0(v_oldState_605_, v_otherState_606_, v_k_607_, v_v_608_);
lean_dec_ref(v_oldState_605_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg(lean_object* v_oldState_610_, lean_object* v_newState_611_, lean_object* v_otherState_612_){
_start:
{
lean_object* v___f_613_; lean_object* v___x_614_; 
v___f_613_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_613_, 0, v_oldState_610_);
v___x_614_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_newState_611_, v___f_613_, v_otherState_612_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___boxed(lean_object* v_oldState_615_, lean_object* v_newState_616_, lean_object* v_otherState_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg(v_oldState_615_, v_newState_616_, v_otherState_617_);
lean_dec_ref(v_newState_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn(lean_object* v_00_u03b2_619_, uint8_t v_phase_620_, lean_object* v_oldState_621_, lean_object* v_newState_622_, lean_object* v_x_623_, lean_object* v_otherState_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg(v_oldState_621_, v_newState_622_, v_otherState_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___boxed(lean_object* v_00_u03b2_626_, lean_object* v_phase_627_, lean_object* v_oldState_628_, lean_object* v_newState_629_, lean_object* v_x_630_, lean_object* v_otherState_631_){
_start:
{
uint8_t v_phase_boxed_632_; lean_object* v_res_633_; 
v_phase_boxed_632_ = lean_unbox(v_phase_627_);
v_res_633_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn(v_00_u03b2_626_, v_phase_boxed_632_, v_oldState_628_, v_newState_629_, v_x_630_, v_otherState_631_);
lean_dec(v_x_630_);
lean_dec_ref(v_newState_629_);
return v_res_633_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0(lean_object* v_00_u03b2_634_, lean_object* v_x_635_, lean_object* v_x_636_){
_start:
{
uint8_t v___x_637_; 
v___x_637_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg(v_x_635_, v_x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___boxed(lean_object* v_00_u03b2_638_, lean_object* v_x_639_, lean_object* v_x_640_){
_start:
{
uint8_t v_res_641_; lean_object* v_r_642_; 
v_res_641_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0(v_00_u03b2_638_, v_x_639_, v_x_640_);
lean_dec(v_x_640_);
lean_dec_ref(v_x_639_);
v_r_642_ = lean_box(v_res_641_);
return v_r_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1(lean_object* v_00_u03b2_643_, lean_object* v_x_644_, lean_object* v_x_645_, lean_object* v_x_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_x_644_, v_x_645_, v_x_646_);
return v___x_647_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0(lean_object* v_00_u03b2_648_, lean_object* v_x_649_, size_t v_x_650_, lean_object* v_x_651_){
_start:
{
uint8_t v___x_652_; 
v___x_652_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg(v_x_649_, v_x_650_, v_x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___boxed(lean_object* v_00_u03b2_653_, lean_object* v_x_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
size_t v_x_746__boxed_657_; uint8_t v_res_658_; lean_object* v_r_659_; 
v_x_746__boxed_657_ = lean_unbox_usize(v_x_655_);
lean_dec(v_x_655_);
v_res_658_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0(v_00_u03b2_653_, v_x_654_, v_x_746__boxed_657_, v_x_656_);
lean_dec(v_x_656_);
lean_dec_ref(v_x_654_);
v_r_659_ = lean_box(v_res_658_);
return v_r_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2(lean_object* v_00_u03b2_660_, lean_object* v_x_661_, size_t v_x_662_, size_t v_x_663_, lean_object* v_x_664_, lean_object* v_x_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_x_661_, v_x_662_, v_x_663_, v_x_664_, v_x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___boxed(lean_object* v_00_u03b2_667_, lean_object* v_x_668_, lean_object* v_x_669_, lean_object* v_x_670_, lean_object* v_x_671_, lean_object* v_x_672_){
_start:
{
size_t v_x_757__boxed_673_; size_t v_x_758__boxed_674_; lean_object* v_res_675_; 
v_x_757__boxed_673_ = lean_unbox_usize(v_x_669_);
lean_dec(v_x_669_);
v_x_758__boxed_674_ = lean_unbox_usize(v_x_670_);
lean_dec(v_x_670_);
v_res_675_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2(v_00_u03b2_667_, v_x_668_, v_x_757__boxed_673_, v_x_758__boxed_674_, v_x_671_, v_x_672_);
return v_res_675_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_676_, lean_object* v_keys_677_, lean_object* v_vals_678_, lean_object* v_heq_679_, lean_object* v_i_680_, lean_object* v_k_681_){
_start:
{
uint8_t v___x_682_; 
v___x_682_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg(v_keys_677_, v_i_680_, v_k_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_683_, lean_object* v_keys_684_, lean_object* v_vals_685_, lean_object* v_heq_686_, lean_object* v_i_687_, lean_object* v_k_688_){
_start:
{
uint8_t v_res_689_; lean_object* v_r_690_; 
v_res_689_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1(v_00_u03b2_683_, v_keys_684_, v_vals_685_, v_heq_686_, v_i_687_, v_k_688_);
lean_dec(v_k_688_);
lean_dec_ref(v_vals_685_);
lean_dec_ref(v_keys_684_);
v_r_690_ = lean_box(v_res_689_);
return v_r_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_691_, lean_object* v_n_692_, lean_object* v_k_693_, lean_object* v_v_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4___redArg(v_n_692_, v_k_693_, v_v_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_696_, size_t v_depth_697_, lean_object* v_keys_698_, lean_object* v_vals_699_, lean_object* v_heq_700_, lean_object* v_i_701_, lean_object* v_entries_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg(v_depth_697_, v_keys_698_, v_vals_699_, v_i_701_, v_entries_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_704_, lean_object* v_depth_705_, lean_object* v_keys_706_, lean_object* v_vals_707_, lean_object* v_heq_708_, lean_object* v_i_709_, lean_object* v_entries_710_){
_start:
{
size_t v_depth_boxed_711_; lean_object* v_res_712_; 
v_depth_boxed_711_ = lean_unbox_usize(v_depth_705_);
lean_dec(v_depth_705_);
v_res_712_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5(v_00_u03b2_704_, v_depth_boxed_711_, v_keys_706_, v_vals_707_, v_heq_708_, v_i_709_, v_entries_710_);
lean_dec_ref(v_vals_707_);
lean_dec_ref(v_keys_706_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_713_, lean_object* v_x_714_, lean_object* v_x_715_, lean_object* v_x_716_, lean_object* v_x_717_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4_spec__5___redArg(v_x_714_, v_x_715_, v_x_716_, v_x_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___lam__0(lean_object* v_count_719_, lean_object* v_x_720_, lean_object* v_x_721_){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_unsigned_to_nat(1u);
v___x_723_ = lean_nat_add(v_count_719_, v___x_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___lam__0___boxed(lean_object* v_count_724_, lean_object* v_x_725_, lean_object* v_x_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___lam__0(v_count_724_, v_x_725_, v_x_726_);
lean_dec(v_x_726_);
lean_dec(v_x_725_);
lean_dec(v_count_724_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg(lean_object* v_state_732_){
_start:
{
lean_object* v___f_733_; lean_object* v___x_734_; lean_object* v_numEntries_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___f_733_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__0));
v___x_734_ = lean_unsigned_to_nat(0u);
v_numEntries_735_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_state_732_, v___f_733_, v___x_734_);
v___x_736_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__2));
v___x_737_ = l_Nat_reprFast(v_numEntries_735_);
v___x_738_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
v___x_739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_736_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___boxed(lean_object* v_state_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg(v_state_740_);
lean_dec_ref(v_state_740_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn(uint8_t v_pu_742_, lean_object* v_00_u03b2_743_, lean_object* v_state_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg(v_state_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___boxed(lean_object* v_pu_746_, lean_object* v_00_u03b2_747_, lean_object* v_state_748_){
_start:
{
uint8_t v_pu_boxed_749_; lean_object* v_res_750_; 
v_pu_boxed_749_ = lean_unbox(v_pu_746_);
v_res_750_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn(v_pu_boxed_749_, v_00_u03b2_747_, v_state_748_);
lean_dec_ref(v_state_748_);
return v_res_750_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___redArg(lean_object* v_a_751_, lean_object* v_b_752_){
_start:
{
lean_object* v_toSignature_753_; lean_object* v_toSignature_754_; lean_object* v_name_755_; lean_object* v_name_756_; uint8_t v___x_757_; 
v_toSignature_753_ = lean_ctor_get(v_a_751_, 0);
v_toSignature_754_ = lean_ctor_get(v_b_752_, 0);
v_name_755_ = lean_ctor_get(v_toSignature_753_, 0);
v_name_756_ = lean_ctor_get(v_toSignature_754_, 0);
v___x_757_ = l_Lean_Name_quickLt(v_name_755_, v_name_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___redArg___boxed(lean_object* v_a_758_, lean_object* v_b_759_){
_start:
{
uint8_t v_res_760_; lean_object* v_r_761_; 
v_res_760_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___redArg(v_a_758_, v_b_759_);
lean_dec_ref(v_b_759_);
lean_dec_ref(v_a_758_);
v_r_761_ = lean_box(v_res_760_);
return v_r_761_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt(uint8_t v_pu_762_, lean_object* v_a_763_, lean_object* v_b_764_){
_start:
{
lean_object* v_toSignature_765_; lean_object* v_toSignature_766_; lean_object* v_name_767_; lean_object* v_name_768_; uint8_t v___x_769_; 
v_toSignature_765_ = lean_ctor_get(v_a_763_, 0);
v_toSignature_766_ = lean_ctor_get(v_b_764_, 0);
v_name_767_ = lean_ctor_get(v_toSignature_765_, 0);
v_name_768_ = lean_ctor_get(v_toSignature_766_, 0);
v___x_769_ = l_Lean_Name_quickLt(v_name_767_, v_name_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___boxed(lean_object* v_pu_770_, lean_object* v_a_771_, lean_object* v_b_772_){
_start:
{
uint8_t v_pu_boxed_773_; uint8_t v_res_774_; lean_object* v_r_775_; 
v_pu_boxed_773_ = lean_unbox(v_pu_770_);
v_res_774_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt(v_pu_boxed_773_, v_a_771_, v_b_772_);
lean_dec_ref(v_b_772_);
lean_dec_ref(v_a_771_);
v_r_775_ = lean_box(v_res_774_);
return v_r_775_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0(void){
_start:
{
lean_object* v_tmpDecl_776_; 
v_tmpDecl_776_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default___redArg();
return v_tmpDecl_776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f(uint8_t v_pu_778_, lean_object* v_decls_779_, lean_object* v_declName_780_){
_start:
{
lean_object* v_tmpDecl_781_; lean_object* v_toSignature_782_; lean_object* v_value_783_; uint8_t v_recursive_784_; lean_object* v_inlineAttr_x3f_785_; lean_object* v_levelParams_786_; lean_object* v_type_787_; lean_object* v_params_788_; uint8_t v_safe_789_; lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v_tmpDecl_781_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0, &l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0_once, _init_l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0);
v_toSignature_782_ = lean_ctor_get(v_tmpDecl_781_, 0);
v_value_783_ = lean_ctor_get(v_tmpDecl_781_, 1);
v_recursive_784_ = lean_ctor_get_uint8(v_tmpDecl_781_, sizeof(void*)*3);
v_inlineAttr_x3f_785_ = lean_ctor_get(v_tmpDecl_781_, 2);
v_levelParams_786_ = lean_ctor_get(v_toSignature_782_, 1);
v_type_787_ = lean_ctor_get(v_toSignature_782_, 2);
v_params_788_ = lean_ctor_get(v_toSignature_782_, 3);
v_safe_789_ = lean_ctor_get_uint8(v_toSignature_782_, sizeof(void*)*4);
v___x_790_ = lean_unsigned_to_nat(0u);
v___x_791_ = lean_array_get_size(v_decls_779_);
v___x_792_ = lean_nat_dec_lt(v___x_790_, v___x_791_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; 
lean_dec(v_declName_780_);
v___x_793_ = lean_box(0);
return v___x_793_;
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_794_ = lean_unsigned_to_nat(1u);
v___x_795_ = lean_nat_sub(v___x_791_, v___x_794_);
v___x_796_ = lean_nat_dec_le(v___x_790_, v___x_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; 
lean_dec(v___x_795_);
lean_dec(v_declName_780_);
v___x_797_ = lean_box(0);
return v___x_797_;
}
else
{
lean_object* v___x_798_; lean_object* v_tmpDecl_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
lean_inc_ref(v_params_788_);
lean_inc_ref(v_type_787_);
lean_inc(v_levelParams_786_);
v___x_798_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_798_, 0, v_declName_780_);
lean_ctor_set(v___x_798_, 1, v_levelParams_786_);
lean_ctor_set(v___x_798_, 2, v_type_787_);
lean_ctor_set(v___x_798_, 3, v_params_788_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*4, v_safe_789_);
lean_inc(v_inlineAttr_x3f_785_);
lean_inc_ref(v_value_783_);
v_tmpDecl_799_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_tmpDecl_799_, 0, v___x_798_);
lean_ctor_set(v_tmpDecl_799_, 1, v_value_783_);
lean_ctor_set(v_tmpDecl_799_, 2, v_inlineAttr_x3f_785_);
lean_ctor_set_uint8(v_tmpDecl_799_, sizeof(void*)*3, v_recursive_784_);
v___x_800_ = lean_box(v_pu_778_);
v___x_801_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___boxed), 3, 1);
lean_closure_set(v___x_801_, 0, v___x_800_);
v___x_802_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__1));
v___x_803_ = l_Array_binSearchAux___redArg(v___x_801_, v___x_802_, v_decls_779_, v_tmpDecl_799_, v___x_790_, v___x_795_);
return v___x_803_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___boxed(lean_object* v_pu_804_, lean_object* v_decls_805_, lean_object* v_declName_806_){
_start:
{
uint8_t v_pu_boxed_807_; lean_object* v_res_808_; 
v_pu_boxed_807_ = lean_unbox(v_pu_804_);
v_res_808_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f(v_pu_boxed_807_, v_decls_805_, v_declName_806_);
lean_dec_ref(v_decls_805_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__0(lean_object* v_x_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__0___closed__1));
v___x_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__0___boxed(lean_object* v_x_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__0(v_x_817_, v___y_818_);
lean_dec_ref(v___y_818_);
lean_dec_ref(v_x_817_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__1(lean_object* v_s_821_, lean_object* v_x_822_){
_start:
{
lean_inc_ref(v_s_821_);
return v_s_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__1___boxed(lean_object* v_s_823_, lean_object* v_x_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__1(v_s_823_, v_x_824_);
lean_dec_ref(v_x_824_);
lean_dec_ref(v_s_823_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__2(lean_object* v_x_830_, lean_object* v_x_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__2___closed__1));
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__2___boxed(lean_object* v_x_833_, lean_object* v_x_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__2(v_x_833_, v_x_834_);
lean_dec_ref(v_x_834_);
lean_dec_ref(v_x_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__3(lean_object* v_x_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = lean_box(0);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__3___boxed(lean_object* v_x_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__3(v_x_838_);
lean_dec_ref(v_x_838_);
return v_res_839_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_844_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__5(void){
_start:
{
lean_object* v___f_845_; lean_object* v___f_846_; lean_object* v___f_847_; lean_object* v___f_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___f_845_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__3));
v___f_846_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__2));
v___f_847_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__1));
v___f_848_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__0));
v___x_849_ = lean_box(0);
v___x_850_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__4, &l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__4);
v___x_851_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v___x_849_);
lean_ctor_set(v___x_851_, 2, v___f_848_);
lean_ctor_set(v___x_851_, 3, v___f_847_);
lean_ctor_set(v___x_851_, 4, v___f_846_);
lean_ctor_set(v___x_851_, 5, v___f_845_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg(){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__5, &l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__5);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___boxed(lean_object* v___dummy_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg();
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1(uint8_t v_pu_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__5, &l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__5);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___boxed(lean_object* v_pu_858_){
_start:
{
uint8_t v_pu_boxed_859_; lean_object* v_res_860_; 
v_pu_boxed_859_ = lean_unbox(v_pu_858_);
v_res_860_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1(v_pu_boxed_859_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___redArg(){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__5, &l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__5);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___redArg___boxed(lean_object* v___dummy_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___redArg();
return v_res_864_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__0(void){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___redArg();
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt(uint8_t v_pu_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__0, &l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__0);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___boxed(lean_object* v_pu_868_){
_start:
{
uint8_t v_pu_boxed_869_; lean_object* v_res_870_; 
v_pu_boxed_869_ = lean_unbox(v_pu_868_);
v_res_870_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt(v_pu_boxed_869_);
return v_res_870_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__10));
v___x_898_ = l_Lean_mkAtom(v___x_897_);
return v___x_898_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_899_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12);
v___x_900_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5));
v___x_901_ = lean_array_push(v___x_900_, v___x_899_);
return v___x_901_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__17));
v___x_911_ = l_Lean_mkAtom(v___x_910_);
return v___x_911_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_912_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18);
v___x_913_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5));
v___x_914_ = lean_array_push(v___x_913_, v___x_912_);
return v___x_914_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_915_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19);
v___x_916_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16));
v___x_917_ = lean_box(2);
v___x_918_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
lean_ctor_set(v___x_918_, 1, v___x_916_);
lean_ctor_set(v___x_918_, 2, v___x_915_);
return v___x_918_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_919_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20);
v___x_920_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13);
v___x_921_ = lean_array_push(v___x_920_, v___x_919_);
return v___x_921_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_922_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21);
v___x_923_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11));
v___x_924_ = lean_box(2);
v___x_925_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
lean_ctor_set(v___x_925_, 1, v___x_923_);
lean_ctor_set(v___x_925_, 2, v___x_922_);
return v___x_925_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_926_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22);
v___x_927_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5));
v___x_928_ = lean_array_push(v___x_927_, v___x_926_);
return v___x_928_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_929_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23);
v___x_930_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__9));
v___x_931_ = lean_box(2);
v___x_932_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
lean_ctor_set(v___x_932_, 1, v___x_930_);
lean_ctor_set(v___x_932_, 2, v___x_929_);
return v___x_932_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_933_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24);
v___x_934_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5));
v___x_935_ = lean_array_push(v___x_934_, v___x_933_);
return v___x_935_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_936_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25);
v___x_937_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7));
v___x_938_ = lean_box(2);
v___x_939_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v___x_937_);
lean_ctor_set(v___x_939_, 2, v___x_936_);
return v___x_939_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_940_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26);
v___x_941_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5));
v___x_942_ = lean_array_push(v___x_941_, v___x_940_);
return v___x_942_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_943_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27);
v___x_944_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4));
v___x_945_ = lean_box(2);
v___x_946_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v___x_944_);
lean_ctor_set(v___x_946_, 2, v___x_943_);
return v___x_946_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1(void){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__0(lean_object* v_s_948_, lean_object* v_decl_949_){
_start:
{
lean_object* v_toSignature_950_; lean_object* v_name_951_; lean_object* v___x_952_; 
v_toSignature_950_ = lean_ctor_get(v_decl_949_, 0);
v_name_951_ = lean_ctor_get(v_toSignature_950_, 0);
lean_inc(v_name_951_);
v___x_952_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_s_948_, v_name_951_, v_decl_949_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__1(lean_object* v_x_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__2___closed__0));
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__1___boxed(lean_object* v_x_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__1(v_x_955_);
lean_dec_ref(v_x_955_);
return v_res_956_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_mkDeclExt___lam__2(lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_toSignature_959_; lean_object* v_toSignature_960_; lean_object* v_name_961_; lean_object* v_name_962_; uint8_t v___x_963_; 
v_toSignature_959_ = lean_ctor_get(v___y_957_, 0);
v_toSignature_960_ = lean_ctor_get(v___y_958_, 0);
v_name_961_ = lean_ctor_get(v_toSignature_959_, 0);
v_name_962_ = lean_ctor_get(v_toSignature_960_, 0);
v___x_963_ = l_Lean_Name_quickLt(v_name_961_, v_name_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__2___boxed(lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
uint8_t v_res_966_; lean_object* v_r_967_; 
v_res_966_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__2(v___y_964_, v___y_965_);
lean_dec_ref(v___y_965_);
lean_dec_ref(v___y_964_);
v_r_967_ = lean_box(v_res_966_);
return v_r_967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(lean_object* v_env_973_, uint8_t v_phase_974_, lean_object* v_as_975_, size_t v_i_976_, size_t v_stop_977_, lean_object* v_b_978_){
_start:
{
lean_object* v___y_980_; uint8_t v___x_984_; 
v___x_984_ = lean_usize_dec_eq(v_i_976_, v_stop_977_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; lean_object* v_toSignature_986_; uint8_t v_recursive_987_; lean_object* v_inlineAttr_x3f_988_; lean_object* v_name_989_; uint8_t v___x_990_; 
v___x_985_ = lean_array_uget(v_as_975_, v_i_976_);
v_toSignature_986_ = lean_ctor_get(v___x_985_, 0);
v_recursive_987_ = lean_ctor_get_uint8(v___x_985_, sizeof(void*)*3);
v_inlineAttr_x3f_988_ = lean_ctor_get(v___x_985_, 2);
v_name_989_ = lean_ctor_get(v_toSignature_986_, 0);
lean_inc_ref(v_env_973_);
v___x_990_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_973_, v_name_989_);
if (v___x_990_ == 0)
{
lean_dec(v___x_985_);
v___y_980_ = v_b_978_;
goto v___jp_979_;
}
else
{
uint8_t v___x_991_; 
lean_inc_ref(v_env_973_);
v___x_991_ = l_Lean_Compiler_LCNF_isDeclTransparent(v_env_973_, v_phase_974_, v_name_989_);
if (v___x_991_ == 0)
{
lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1000_; 
lean_inc(v_inlineAttr_x3f_988_);
lean_inc_ref(v_toSignature_986_);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1000_ == 0)
{
lean_object* v_unused_1001_; lean_object* v_unused_1002_; lean_object* v_unused_1003_; 
v_unused_1001_ = lean_ctor_get(v___x_985_, 2);
lean_dec(v_unused_1001_);
v_unused_1002_ = lean_ctor_get(v___x_985_, 1);
lean_dec(v_unused_1002_);
v_unused_1003_ = lean_ctor_get(v___x_985_, 0);
lean_dec(v_unused_1003_);
v___x_993_ = v___x_985_;
v_isShared_994_ = v_isSharedCheck_1000_;
goto v_resetjp_992_;
}
else
{
lean_dec(v___x_985_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1000_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_995_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__1));
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 1, v___x_995_);
v___x_997_ = v___x_993_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_toSignature_986_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v_inlineAttr_x3f_988_);
lean_ctor_set_uint8(v_reuseFailAlloc_999_, sizeof(void*)*3, v_recursive_987_);
v___x_997_ = v_reuseFailAlloc_999_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_998_; 
v___x_998_ = lean_array_push(v_b_978_, v___x_997_);
v___y_980_ = v___x_998_;
goto v___jp_979_;
}
}
}
else
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_array_push(v_b_978_, v___x_985_);
v___y_980_ = v___x_1004_;
goto v___jp_979_;
}
}
}
else
{
lean_dec_ref(v_env_973_);
return v_b_978_;
}
v___jp_979_:
{
size_t v___x_981_; size_t v___x_982_; 
v___x_981_ = ((size_t)1ULL);
v___x_982_ = lean_usize_add(v_i_976_, v___x_981_);
v_i_976_ = v___x_982_;
v_b_978_ = v___y_980_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___boxed(lean_object* v_env_1005_, lean_object* v_phase_1006_, lean_object* v_as_1007_, lean_object* v_i_1008_, lean_object* v_stop_1009_, lean_object* v_b_1010_){
_start:
{
uint8_t v_phase_boxed_1011_; size_t v_i_boxed_1012_; size_t v_stop_boxed_1013_; lean_object* v_res_1014_; 
v_phase_boxed_1011_ = lean_unbox(v_phase_1006_);
v_i_boxed_1012_ = lean_unbox_usize(v_i_1008_);
lean_dec(v_i_1008_);
v_stop_boxed_1013_ = lean_unbox_usize(v_stop_1009_);
lean_dec(v_stop_1009_);
v_res_1014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(v_env_1005_, v_phase_boxed_1011_, v_as_1007_, v_i_boxed_1012_, v_stop_boxed_1013_, v_b_1010_);
lean_dec_ref(v_as_1007_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0(lean_object* v_env_1015_, uint8_t v_phase_1016_, uint8_t v___x_1017_, lean_object* v_as_1018_, lean_object* v_start_1019_, lean_object* v_stop_1020_){
_start:
{
lean_object* v___x_1021_; uint8_t v___x_1022_; 
v___x_1021_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__2___closed__0));
v___x_1022_ = lean_nat_dec_lt(v_start_1019_, v_stop_1020_);
if (v___x_1022_ == 0)
{
lean_dec_ref(v_env_1015_);
return v___x_1021_;
}
else
{
lean_object* v___x_1023_; uint8_t v___x_1024_; 
v___x_1023_ = lean_array_get_size(v_as_1018_);
v___x_1024_ = lean_nat_dec_le(v_stop_1020_, v___x_1023_);
if (v___x_1024_ == 0)
{
uint8_t v___x_1025_; 
v___x_1025_ = lean_nat_dec_lt(v_start_1019_, v___x_1023_);
if (v___x_1025_ == 0)
{
lean_dec_ref(v_env_1015_);
return v___x_1021_;
}
else
{
size_t v___x_1026_; size_t v___x_1027_; lean_object* v___x_1028_; 
v___x_1026_ = lean_usize_of_nat(v_start_1019_);
v___x_1027_ = lean_usize_of_nat(v___x_1023_);
v___x_1028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(v_env_1015_, v_phase_1016_, v_as_1018_, v___x_1026_, v___x_1027_, v___x_1021_);
return v___x_1028_;
}
}
else
{
size_t v___x_1029_; size_t v___x_1030_; lean_object* v___x_1031_; 
v___x_1029_ = lean_usize_of_nat(v_start_1019_);
v___x_1030_ = lean_usize_of_nat(v_stop_1020_);
v___x_1031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(v_env_1015_, v_phase_1016_, v_as_1018_, v___x_1029_, v___x_1030_, v___x_1021_);
return v___x_1031_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0___boxed(lean_object* v_env_1032_, lean_object* v_phase_1033_, lean_object* v___x_1034_, lean_object* v_as_1035_, lean_object* v_start_1036_, lean_object* v_stop_1037_){
_start:
{
uint8_t v_phase_boxed_1038_; uint8_t v___x_972__boxed_1039_; lean_object* v_res_1040_; 
v_phase_boxed_1038_ = lean_unbox(v_phase_1033_);
v___x_972__boxed_1039_ = lean_unbox(v___x_1034_);
v_res_1040_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0(v_env_1032_, v_phase_boxed_1038_, v___x_972__boxed_1039_, v_as_1035_, v_start_1036_, v_stop_1037_);
lean_dec(v_stop_1037_);
lean_dec(v_start_1036_);
lean_dec_ref(v_as_1035_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__3(uint8_t v_phase_1041_, lean_object* v___f_1042_, lean_object* v_env_1043_, lean_object* v_s_1044_){
_start:
{
uint8_t v___x_1045_; lean_object* v_all_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v_exported_1049_; lean_object* v___x_1050_; 
v___x_1045_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_1041_);
v_all_1046_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(v_s_1044_, v___f_1042_);
v___x_1047_ = lean_unsigned_to_nat(0u);
v___x_1048_ = lean_array_get_size(v_all_1046_);
v_exported_1049_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0(v_env_1043_, v_phase_1041_, v___x_1045_, v_all_1046_, v___x_1047_, v___x_1048_);
lean_inc_ref(v_exported_1049_);
v___x_1050_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1050_, 0, v_exported_1049_);
lean_ctor_set(v___x_1050_, 1, v_exported_1049_);
lean_ctor_set(v___x_1050_, 2, v_all_1046_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__3___boxed(lean_object* v_phase_1051_, lean_object* v___f_1052_, lean_object* v_env_1053_, lean_object* v_s_1054_){
_start:
{
uint8_t v_phase_boxed_1055_; lean_object* v_res_1056_; 
v_phase_boxed_1055_ = lean_unbox(v_phase_1051_);
v_res_1056_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__3(v_phase_boxed_1055_, v___f_1052_, v_env_1053_, v_s_1054_);
lean_dec_ref(v_s_1054_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__4(lean_object* v___x_1057_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1057_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__4___boxed(lean_object* v___x_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__4(v___x_1060_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__5(lean_object* v___x_1063_, lean_object* v_x_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1063_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__5___boxed(lean_object* v___x_1068_, lean_object* v_x_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__5(v___x_1068_, v_x_1069_, v___y_1070_);
lean_dec_ref(v___y_1070_);
lean_dec_ref(v_x_1069_);
return v_res_1072_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__3(void){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__4(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__3, &l_Lean_Compiler_LCNF_mkDeclExt___closed__3_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__3);
v___x_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
return v___x_1078_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__5(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___f_1080_; 
v___x_1079_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__4, &l_Lean_Compiler_LCNF_mkDeclExt___closed__4_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__4);
v___f_1080_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkDeclExt___lam__4___boxed), 2, 1);
lean_closure_set(v___f_1080_, 0, v___x_1079_);
return v___f_1080_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__6(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___f_1082_; 
v___x_1081_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__4, &l_Lean_Compiler_LCNF_mkDeclExt___closed__4_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__4);
v___f_1082_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkDeclExt___lam__5___boxed), 4, 1);
lean_closure_set(v___f_1082_, 0, v___x_1081_);
return v___f_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt(uint8_t v_phase_1083_, lean_object* v_name_1084_){
_start:
{
lean_object* v___f_1086_; lean_object* v___f_1087_; lean_object* v___f_1088_; lean_object* v___x_1089_; lean_object* v___f_1090_; lean_object* v___f_1091_; lean_object* v___f_1092_; uint8_t v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___f_1086_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___closed__0));
v___f_1087_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___closed__1));
v___f_1088_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___closed__2));
v___x_1089_ = lean_box(v_phase_1083_);
v___f_1090_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkDeclExt___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1090_, 0, v___x_1089_);
lean_closure_set(v___f_1090_, 1, v___f_1088_);
v___f_1091_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__5, &l_Lean_Compiler_LCNF_mkDeclExt___closed__5_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__5);
v___f_1092_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__6, &l_Lean_Compiler_LCNF_mkDeclExt___closed__6_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__6);
v___x_1093_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_1083_);
v___x_1094_ = lean_box(v___x_1093_);
v___x_1095_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___boxed), 3, 2);
lean_closure_set(v___x_1095_, 0, v___x_1094_);
lean_closure_set(v___x_1095_, 1, lean_box(0));
v___x_1096_ = lean_box(0);
v___x_1097_ = lean_box(v_phase_1083_);
v___x_1098_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___boxed), 6, 2);
lean_closure_set(v___x_1098_, 0, lean_box(0));
lean_closure_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
v___x_1100_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1100_, 0, v_name_1084_);
lean_ctor_set(v___x_1100_, 1, v___f_1091_);
lean_ctor_set(v___x_1100_, 2, v___f_1092_);
lean_ctor_set(v___x_1100_, 3, v___f_1086_);
lean_ctor_set(v___x_1100_, 4, v___f_1090_);
lean_ctor_set(v___x_1100_, 5, v___x_1095_);
lean_ctor_set(v___x_1100_, 6, v___x_1096_);
lean_ctor_set(v___x_1100_, 7, v___x_1099_);
v___x_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
lean_ctor_set(v___x_1101_, 1, v___f_1087_);
v___x_1102_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___boxed(lean_object* v_phase_1103_, lean_object* v_name_1104_, lean_object* v_a_1105_){
_start:
{
uint8_t v_phase_boxed_1106_; lean_object* v_res_1107_; 
v_phase_boxed_1106_ = lean_unbox(v_phase_1103_);
v_res_1107_ = l_Lean_Compiler_LCNF_mkDeclExt(v_phase_boxed_1106_, v_name_1104_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0(lean_object* v_env_1108_, uint8_t v_phase_1109_, uint8_t v___x_1110_, lean_object* v_as_1111_, size_t v_i_1112_, size_t v_stop_1113_, lean_object* v_b_1114_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(v_env_1108_, v_phase_1109_, v_as_1111_, v_i_1112_, v_stop_1113_, v_b_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___boxed(lean_object* v_env_1116_, lean_object* v_phase_1117_, lean_object* v___x_1118_, lean_object* v_as_1119_, lean_object* v_i_1120_, lean_object* v_stop_1121_, lean_object* v_b_1122_){
_start:
{
uint8_t v_phase_boxed_1123_; uint8_t v___x_1098__boxed_1124_; size_t v_i_boxed_1125_; size_t v_stop_boxed_1126_; lean_object* v_res_1127_; 
v_phase_boxed_1123_ = lean_unbox(v_phase_1117_);
v___x_1098__boxed_1124_ = lean_unbox(v___x_1118_);
v_i_boxed_1125_ = lean_unbox_usize(v_i_1120_);
lean_dec(v_i_1120_);
v_stop_boxed_1126_ = lean_unbox_usize(v_stop_1121_);
lean_dec(v_stop_1121_);
v_res_1127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0(v_env_1116_, v_phase_boxed_1123_, v___x_1098__boxed_1124_, v_as_1119_, v_i_boxed_1125_, v_stop_boxed_1126_, v_b_1122_);
lean_dec_ref(v_as_1119_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = 0;
v___x_1138_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_));
v___x_1139_ = l_Lean_Compiler_LCNF_mkDeclExt(v___x_1137_, v___x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2____boxed(lean_object* v_a_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_();
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1149_ = 1;
v___x_1150_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_));
v___x_1151_ = l_Lean_Compiler_LCNF_mkDeclExt(v___x_1149_, v___x_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2____boxed(lean_object* v_a_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_();
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___f_1160_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__5, &l_Lean_Compiler_LCNF_mkDeclExt___closed__5_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__5);
v___x_1161_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_));
v___x_1162_ = lean_box(0);
v___x_1163_ = l_Lean_registerEnvExtension___redArg(v___f_1160_, v___x_1161_, v___x_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2____boxed(lean_object* v_a_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_();
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__0(lean_object* v_x_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___lam__0___closed__1));
v___x_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__0___boxed(lean_object* v_x_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__0(v_x_1171_, v___y_1172_);
lean_dec_ref(v___y_1172_);
lean_dec_ref(v_x_1171_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__1(lean_object* v_s_1175_, lean_object* v_x_1176_){
_start:
{
lean_inc_ref(v_s_1175_);
return v_s_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__1___boxed(lean_object* v_s_1177_, lean_object* v_x_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__1(v_s_1177_, v_x_1178_);
lean_dec_ref(v_x_1178_);
lean_dec_ref(v_s_1177_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__2(lean_object* v_x_1184_, lean_object* v_x_1185_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__2___closed__1));
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__2___boxed(lean_object* v_x_1187_, lean_object* v_x_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__2(v_x_1187_, v_x_1188_);
lean_dec_ref(v_x_1188_);
lean_dec_ref(v_x_1187_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__3(lean_object* v_x_1190_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = lean_box(0);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__3___boxed(lean_object* v_x_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__3(v_x_1192_);
lean_dec_ref(v_x_1192_);
return v_res_1193_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__4(void){
_start:
{
lean_object* v___f_1198_; lean_object* v___f_1199_; lean_object* v___f_1200_; lean_object* v___f_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___f_1198_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__3));
v___f_1199_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__2));
v___f_1200_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__1));
v___f_1201_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__0));
v___x_1202_ = lean_box(0);
v___x_1203_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__4, &l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___redArg___closed__4);
v___x_1204_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
lean_ctor_set(v___x_1204_, 1, v___x_1202_);
lean_ctor_set(v___x_1204_, 2, v___f_1201_);
lean_ctor_set(v___x_1204_, 3, v___f_1200_);
lean_ctor_set(v___x_1204_, 4, v___f_1199_);
lean_ctor_set(v___x_1204_, 5, v___f_1198_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg(){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__4, &l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__4);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___boxed(lean_object* v___dummy_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg();
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1(uint8_t v_pu_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__4, &l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__4);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___boxed(lean_object* v_pu_1211_){
_start:
{
uint8_t v_pu_boxed_1212_; lean_object* v_res_1213_; 
v_pu_boxed_1212_ = lean_unbox(v_pu_1211_);
v_res_1213_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1(v_pu_boxed_1212_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___redArg(){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__4, &l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___closed__4);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___redArg___boxed(lean_object* v___dummy_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___redArg();
return v_res_1217_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___closed__0(void){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___redArg();
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt(uint8_t v_pu_1219_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedSigExt___closed__0, &l_Lean_Compiler_LCNF_instInhabitedSigExt___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___closed__0);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___boxed(lean_object* v_pu_1221_){
_start:
{
uint8_t v_pu_boxed_1222_; lean_object* v_res_1223_; 
v_pu_boxed_1222_ = lean_unbox(v_pu_1221_);
v_res_1223_ = l_Lean_Compiler_LCNF_instInhabitedSigExt(v_pu_boxed_1222_);
return v_res_1223_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___redArg(lean_object* v_a_1224_, lean_object* v_b_1225_){
_start:
{
lean_object* v_name_1226_; lean_object* v_name_1227_; uint8_t v___x_1228_; 
v_name_1226_ = lean_ctor_get(v_a_1224_, 0);
v_name_1227_ = lean_ctor_get(v_b_1225_, 0);
v___x_1228_ = l_Lean_Name_quickLt(v_name_1226_, v_name_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___redArg___boxed(lean_object* v_a_1229_, lean_object* v_b_1230_){
_start:
{
uint8_t v_res_1231_; lean_object* v_r_1232_; 
v_res_1231_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___redArg(v_a_1229_, v_b_1230_);
lean_dec_ref(v_b_1230_);
lean_dec_ref(v_a_1229_);
v_r_1232_ = lean_box(v_res_1231_);
return v_r_1232_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt(uint8_t v_pu_1233_, lean_object* v_a_1234_, lean_object* v_b_1235_){
_start:
{
lean_object* v_name_1236_; lean_object* v_name_1237_; uint8_t v___x_1238_; 
v_name_1236_ = lean_ctor_get(v_a_1234_, 0);
v_name_1237_ = lean_ctor_get(v_b_1235_, 0);
v___x_1238_ = l_Lean_Name_quickLt(v_name_1236_, v_name_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___boxed(lean_object* v_pu_1239_, lean_object* v_a_1240_, lean_object* v_b_1241_){
_start:
{
uint8_t v_pu_boxed_1242_; uint8_t v_res_1243_; lean_object* v_r_1244_; 
v_pu_boxed_1242_ = lean_unbox(v_pu_1239_);
v_res_1243_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt(v_pu_boxed_1242_, v_a_1240_, v_b_1241_);
lean_dec_ref(v_b_1241_);
lean_dec_ref(v_a_1240_);
v_r_1244_ = lean_box(v_res_1243_);
return v_r_1244_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0(void){
_start:
{
lean_object* v_tmpSig_1245_; 
v_tmpSig_1245_ = l_Lean_Compiler_LCNF_instInhabitedSignature_default___redArg();
return v_tmpSig_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f(uint8_t v_pu_1247_, lean_object* v_sigs_1248_, lean_object* v_declName_1249_){
_start:
{
lean_object* v_tmpSig_1250_; lean_object* v_levelParams_1251_; lean_object* v_type_1252_; lean_object* v_params_1253_; uint8_t v_safe_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; 
v_tmpSig_1250_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0, &l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0_once, _init_l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0);
v_levelParams_1251_ = lean_ctor_get(v_tmpSig_1250_, 1);
v_type_1252_ = lean_ctor_get(v_tmpSig_1250_, 2);
v_params_1253_ = lean_ctor_get(v_tmpSig_1250_, 3);
v_safe_1254_ = lean_ctor_get_uint8(v_tmpSig_1250_, sizeof(void*)*4);
v___x_1255_ = lean_unsigned_to_nat(0u);
v___x_1256_ = lean_array_get_size(v_sigs_1248_);
v___x_1257_ = lean_nat_dec_lt(v___x_1255_, v___x_1256_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; 
lean_dec(v_declName_1249_);
v___x_1258_ = lean_box(0);
return v___x_1258_;
}
else
{
lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v___x_1259_ = lean_unsigned_to_nat(1u);
v___x_1260_ = lean_nat_sub(v___x_1256_, v___x_1259_);
v___x_1261_ = lean_nat_dec_le(v___x_1255_, v___x_1260_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; 
lean_dec(v___x_1260_);
lean_dec(v_declName_1249_);
v___x_1262_ = lean_box(0);
return v___x_1262_;
}
else
{
lean_object* v_tmpSig_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
lean_inc_ref(v_params_1253_);
lean_inc_ref(v_type_1252_);
lean_inc(v_levelParams_1251_);
v_tmpSig_1263_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_tmpSig_1263_, 0, v_declName_1249_);
lean_ctor_set(v_tmpSig_1263_, 1, v_levelParams_1251_);
lean_ctor_set(v_tmpSig_1263_, 2, v_type_1252_);
lean_ctor_set(v_tmpSig_1263_, 3, v_params_1253_);
lean_ctor_set_uint8(v_tmpSig_1263_, sizeof(void*)*4, v_safe_1254_);
v___x_1264_ = lean_box(v_pu_1247_);
v___x_1265_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___boxed), 3, 1);
lean_closure_set(v___x_1265_, 0, v___x_1264_);
v___x_1266_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__1));
v___x_1267_ = l_Array_binSearchAux___redArg(v___x_1265_, v___x_1266_, v_sigs_1248_, v_tmpSig_1263_, v___x_1255_, v___x_1260_);
return v___x_1267_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___boxed(lean_object* v_pu_1268_, lean_object* v_sigs_1269_, lean_object* v_declName_1270_){
_start:
{
uint8_t v_pu_boxed_1271_; lean_object* v_res_1272_; 
v_pu_boxed_1271_ = lean_unbox(v_pu_1268_);
v_res_1272_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f(v_pu_boxed_1271_, v_sigs_1269_, v_declName_1270_);
lean_dec_ref(v_sigs_1269_);
return v_res_1272_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkSigDeclExt___auto__1(void){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__0(lean_object* v_s_1274_, lean_object* v_sig_1275_){
_start:
{
lean_object* v_name_1276_; lean_object* v___x_1277_; 
v_name_1276_ = lean_ctor_get(v_sig_1275_, 0);
lean_inc(v_name_1276_);
v___x_1277_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_s_1274_, v_name_1276_, v_sig_1275_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1(lean_object* v_x_1278_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__2___closed__0));
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1___boxed(lean_object* v_x_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1(v_x_1280_);
lean_dec_ref(v_x_1280_);
return v_res_1281_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2(lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_name_1284_; lean_object* v_name_1285_; uint8_t v___x_1286_; 
v_name_1284_ = lean_ctor_get(v___y_1282_, 0);
v_name_1285_ = lean_ctor_get(v___y_1283_, 0);
v___x_1286_ = l_Lean_Name_quickLt(v_name_1284_, v_name_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2___boxed(lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
uint8_t v_res_1289_; lean_object* v_r_1290_; 
v_res_1289_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2(v___y_1287_, v___y_1288_);
lean_dec_ref(v___y_1288_);
lean_dec_ref(v___y_1287_);
v_r_1290_ = lean_box(v_res_1289_);
return v_r_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0(lean_object* v_env_1291_, lean_object* v_as_1292_, size_t v_i_1293_, size_t v_stop_1294_, lean_object* v_b_1295_){
_start:
{
lean_object* v___y_1297_; uint8_t v___x_1301_; 
v___x_1301_ = lean_usize_dec_eq(v_i_1293_, v_stop_1294_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; lean_object* v_name_1303_; uint8_t v___x_1304_; 
v___x_1302_ = lean_array_uget_borrowed(v_as_1292_, v_i_1293_);
v_name_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc_ref(v_env_1291_);
v___x_1304_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_1291_, v_name_1303_);
if (v___x_1304_ == 0)
{
v___y_1297_ = v_b_1295_;
goto v___jp_1296_;
}
else
{
lean_object* v___x_1305_; 
lean_inc(v___x_1302_);
v___x_1305_ = lean_array_push(v_b_1295_, v___x_1302_);
v___y_1297_ = v___x_1305_;
goto v___jp_1296_;
}
}
else
{
lean_dec_ref(v_env_1291_);
return v_b_1295_;
}
v___jp_1296_:
{
size_t v___x_1298_; size_t v___x_1299_; 
v___x_1298_ = ((size_t)1ULL);
v___x_1299_ = lean_usize_add(v_i_1293_, v___x_1298_);
v_i_1293_ = v___x_1299_;
v_b_1295_ = v___y_1297_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0___boxed(lean_object* v_env_1306_, lean_object* v_as_1307_, lean_object* v_i_1308_, lean_object* v_stop_1309_, lean_object* v_b_1310_){
_start:
{
size_t v_i_boxed_1311_; size_t v_stop_boxed_1312_; lean_object* v_res_1313_; 
v_i_boxed_1311_ = lean_unbox_usize(v_i_1308_);
lean_dec(v_i_1308_);
v_stop_boxed_1312_ = lean_unbox_usize(v_stop_1309_);
lean_dec(v_stop_1309_);
v_res_1313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0(v_env_1306_, v_as_1307_, v_i_boxed_1311_, v_stop_boxed_1312_, v_b_1310_);
lean_dec_ref(v_as_1307_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0(lean_object* v_env_1314_, lean_object* v_as_1315_, lean_object* v_start_1316_, lean_object* v_stop_1317_){
_start:
{
lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1318_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___redArg___lam__2___closed__0));
v___x_1319_ = lean_nat_dec_lt(v_start_1316_, v_stop_1317_);
if (v___x_1319_ == 0)
{
lean_dec_ref(v_env_1314_);
return v___x_1318_;
}
else
{
lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1320_ = lean_array_get_size(v_as_1315_);
v___x_1321_ = lean_nat_dec_le(v_stop_1317_, v___x_1320_);
if (v___x_1321_ == 0)
{
uint8_t v___x_1322_; 
v___x_1322_ = lean_nat_dec_lt(v_start_1316_, v___x_1320_);
if (v___x_1322_ == 0)
{
lean_dec_ref(v_env_1314_);
return v___x_1318_;
}
else
{
size_t v___x_1323_; size_t v___x_1324_; lean_object* v___x_1325_; 
v___x_1323_ = lean_usize_of_nat(v_start_1316_);
v___x_1324_ = lean_usize_of_nat(v___x_1320_);
v___x_1325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0(v_env_1314_, v_as_1315_, v___x_1323_, v___x_1324_, v___x_1318_);
return v___x_1325_;
}
}
else
{
size_t v___x_1326_; size_t v___x_1327_; lean_object* v___x_1328_; 
v___x_1326_ = lean_usize_of_nat(v_start_1316_);
v___x_1327_ = lean_usize_of_nat(v_stop_1317_);
v___x_1328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0(v_env_1314_, v_as_1315_, v___x_1326_, v___x_1327_, v___x_1318_);
return v___x_1328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0___boxed(lean_object* v_env_1329_, lean_object* v_as_1330_, lean_object* v_start_1331_, lean_object* v_stop_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0(v_env_1329_, v_as_1330_, v_start_1331_, v_stop_1332_);
lean_dec(v_stop_1332_);
lean_dec(v_start_1331_);
lean_dec_ref(v_as_1330_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3(lean_object* v___f_1334_, lean_object* v_env_1335_, lean_object* v_s_1336_){
_start:
{
lean_object* v_all_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v_exported_1340_; lean_object* v___x_1341_; 
v_all_1337_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(v_s_1336_, v___f_1334_);
v___x_1338_ = lean_unsigned_to_nat(0u);
v___x_1339_ = lean_array_get_size(v_all_1337_);
v_exported_1340_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0(v_env_1335_, v_all_1337_, v___x_1338_, v___x_1339_);
lean_inc_ref(v_exported_1340_);
v___x_1341_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1341_, 0, v_exported_1340_);
lean_ctor_set(v___x_1341_, 1, v_exported_1340_);
lean_ctor_set(v___x_1341_, 2, v_all_1337_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3___boxed(lean_object* v___f_1342_, lean_object* v_env_1343_, lean_object* v_s_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3(v___f_1342_, v_env_1343_, v_s_1344_);
lean_dec_ref(v_s_1344_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__4(lean_object* v___x_1346_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1346_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__4___boxed(lean_object* v___x_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__4(v___x_1349_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__5(lean_object* v___x_1352_, lean_object* v_x_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1352_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__5___boxed(lean_object* v___x_1357_, lean_object* v_x_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__5(v___x_1357_, v_x_1358_, v___y_1359_);
lean_dec_ref(v___y_1359_);
lean_dec_ref(v_x_1358_);
return v_res_1361_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4(void){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__3, &l_Lean_Compiler_LCNF_mkDeclExt___closed__3_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__3);
v___x_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
return v___x_1368_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5(void){
_start:
{
lean_object* v___x_1369_; lean_object* v___f_1370_; 
v___x_1369_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4, &l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4_once, _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4);
v___f_1370_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkSigDeclExt___lam__4___boxed), 2, 1);
lean_closure_set(v___f_1370_, 0, v___x_1369_);
return v___f_1370_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6(void){
_start:
{
lean_object* v___x_1371_; lean_object* v___f_1372_; 
v___x_1371_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4, &l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4_once, _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4);
v___f_1372_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkSigDeclExt___lam__5___boxed), 4, 1);
lean_closure_set(v___f_1372_, 0, v___x_1371_);
return v___f_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt(uint8_t v_phase_1373_, lean_object* v_name_1374_){
_start:
{
lean_object* v___f_1376_; lean_object* v___f_1377_; lean_object* v___f_1378_; lean_object* v___f_1379_; lean_object* v___f_1380_; uint8_t v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___f_1376_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__0));
v___f_1377_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__1));
v___f_1378_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__3));
v___f_1379_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5, &l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5_once, _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5);
v___f_1380_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6, &l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6_once, _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6);
v___x_1381_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_1373_);
v___x_1382_ = lean_box(v___x_1381_);
v___x_1383_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___boxed), 3, 2);
lean_closure_set(v___x_1383_, 0, v___x_1382_);
lean_closure_set(v___x_1383_, 1, lean_box(0));
v___x_1384_ = lean_box(0);
v___x_1385_ = lean_box(v_phase_1373_);
v___x_1386_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___boxed), 6, 2);
lean_closure_set(v___x_1386_, 0, lean_box(0));
lean_closure_set(v___x_1386_, 1, v___x_1385_);
v___x_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
v___x_1388_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1388_, 0, v_name_1374_);
lean_ctor_set(v___x_1388_, 1, v___f_1379_);
lean_ctor_set(v___x_1388_, 2, v___f_1380_);
lean_ctor_set(v___x_1388_, 3, v___f_1376_);
lean_ctor_set(v___x_1388_, 4, v___f_1378_);
lean_ctor_set(v___x_1388_, 5, v___x_1383_);
lean_ctor_set(v___x_1388_, 6, v___x_1384_);
lean_ctor_set(v___x_1388_, 7, v___x_1387_);
v___x_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
lean_ctor_set(v___x_1389_, 1, v___f_1377_);
v___x_1390_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1389_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___boxed(lean_object* v_phase_1391_, lean_object* v_name_1392_, lean_object* v_a_1393_){
_start:
{
uint8_t v_phase_boxed_1394_; lean_object* v_res_1395_; 
v_phase_boxed_1394_ = lean_unbox(v_phase_1391_);
v_res_1395_ = l_Lean_Compiler_LCNF_mkSigDeclExt(v_phase_boxed_1394_, v_name_1392_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1403_ = 2;
v___x_1404_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_));
v___x_1405_ = l_Lean_Compiler_LCNF_mkSigDeclExt(v___x_1403_, v___x_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2____boxed(lean_object* v_a_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_();
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(lean_object* v_as_1408_, lean_object* v_k_1409_, lean_object* v_x_1410_, lean_object* v_x_1411_){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v_m_1414_; lean_object* v_a_1415_; uint8_t v___x_1416_; 
v___x_1412_ = lean_nat_add(v_x_1410_, v_x_1411_);
v___x_1413_ = lean_unsigned_to_nat(1u);
v_m_1414_ = lean_nat_shiftr(v___x_1412_, v___x_1413_);
lean_dec(v___x_1412_);
v_a_1415_ = lean_array_fget_borrowed(v_as_1408_, v_m_1414_);
v___x_1416_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__2(v_a_1415_, v_k_1409_);
if (v___x_1416_ == 0)
{
uint8_t v___x_1417_; 
lean_dec(v_x_1411_);
v___x_1417_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__2(v_k_1409_, v_a_1415_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; 
lean_dec(v_m_1414_);
lean_dec(v_x_1410_);
lean_inc(v_a_1415_);
v___x_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1418_, 0, v_a_1415_);
return v___x_1418_;
}
else
{
lean_object* v___x_1419_; uint8_t v___x_1420_; lean_object* v___x_1421_; uint8_t v___y_1423_; 
v___x_1419_ = lean_unsigned_to_nat(0u);
v___x_1420_ = lean_nat_dec_eq(v_m_1414_, v___x_1419_);
v___x_1421_ = lean_nat_sub(v_m_1414_, v___x_1413_);
lean_dec(v_m_1414_);
if (v___x_1420_ == 0)
{
uint8_t v___x_1426_; 
v___x_1426_ = lean_nat_dec_lt(v___x_1421_, v_x_1410_);
v___y_1423_ = v___x_1426_;
goto v___jp_1422_;
}
else
{
v___y_1423_ = v___x_1420_;
goto v___jp_1422_;
}
v___jp_1422_:
{
if (v___y_1423_ == 0)
{
v_x_1411_ = v___x_1421_;
goto _start;
}
else
{
lean_object* v___x_1425_; 
lean_dec(v___x_1421_);
lean_dec(v_x_1410_);
v___x_1425_ = lean_box(0);
return v___x_1425_;
}
}
}
}
else
{
lean_object* v___x_1427_; uint8_t v___x_1428_; 
lean_dec(v_x_1410_);
v___x_1427_ = lean_nat_add(v_m_1414_, v___x_1413_);
lean_dec(v_m_1414_);
v___x_1428_ = lean_nat_dec_le(v___x_1427_, v_x_1411_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; 
lean_dec(v___x_1427_);
lean_dec(v_x_1411_);
v___x_1429_ = lean_box(0);
return v___x_1429_;
}
else
{
v_x_1410_ = v___x_1427_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg___boxed(lean_object* v_as_1431_, lean_object* v_k_1432_, lean_object* v_x_1433_, lean_object* v_x_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(v_as_1431_, v_k_1432_, v_x_1433_, v_x_1434_);
lean_dec_ref(v_k_1432_);
lean_dec_ref(v_as_1431_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1436_, lean_object* v_vals_1437_, lean_object* v_i_1438_, lean_object* v_k_1439_){
_start:
{
lean_object* v___x_1440_; uint8_t v___x_1441_; 
v___x_1440_ = lean_array_get_size(v_keys_1436_);
v___x_1441_ = lean_nat_dec_lt(v_i_1438_, v___x_1440_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; 
lean_dec(v_i_1438_);
v___x_1442_ = lean_box(0);
return v___x_1442_;
}
else
{
lean_object* v_k_x27_1443_; uint8_t v___x_1444_; 
v_k_x27_1443_ = lean_array_fget_borrowed(v_keys_1436_, v_i_1438_);
v___x_1444_ = lean_name_eq(v_k_1439_, v_k_x27_1443_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = lean_unsigned_to_nat(1u);
v___x_1446_ = lean_nat_add(v_i_1438_, v___x_1445_);
lean_dec(v_i_1438_);
v_i_1438_ = v___x_1446_;
goto _start;
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_array_fget_borrowed(v_vals_1437_, v_i_1438_);
lean_dec(v_i_1438_);
lean_inc(v___x_1448_);
v___x_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
return v___x_1449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1450_, lean_object* v_vals_1451_, lean_object* v_i_1452_, lean_object* v_k_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1450_, v_vals_1451_, v_i_1452_, v_k_1453_);
lean_dec(v_k_1453_);
lean_dec_ref(v_vals_1451_);
lean_dec_ref(v_keys_1450_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg(lean_object* v_x_1455_, size_t v_x_1456_, lean_object* v_x_1457_){
_start:
{
if (lean_obj_tag(v_x_1455_) == 0)
{
lean_object* v_es_1458_; lean_object* v___x_1459_; size_t v___x_1460_; size_t v___x_1461_; lean_object* v_j_1462_; lean_object* v___x_1463_; 
v_es_1458_ = lean_ctor_get(v_x_1455_, 0);
v___x_1459_ = lean_box(2);
v___x_1460_ = ((size_t)31ULL);
v___x_1461_ = lean_usize_land(v_x_1456_, v___x_1460_);
v_j_1462_ = lean_usize_to_nat(v___x_1461_);
v___x_1463_ = lean_array_get_borrowed(v___x_1459_, v_es_1458_, v_j_1462_);
lean_dec(v_j_1462_);
switch(lean_obj_tag(v___x_1463_))
{
case 0:
{
lean_object* v_key_1464_; lean_object* v_val_1465_; uint8_t v___x_1466_; 
v_key_1464_ = lean_ctor_get(v___x_1463_, 0);
v_val_1465_ = lean_ctor_get(v___x_1463_, 1);
v___x_1466_ = lean_name_eq(v_x_1457_, v_key_1464_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; 
v___x_1467_ = lean_box(0);
return v___x_1467_;
}
else
{
lean_object* v___x_1468_; 
lean_inc(v_val_1465_);
v___x_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1468_, 0, v_val_1465_);
return v___x_1468_;
}
}
case 1:
{
lean_object* v_node_1469_; size_t v___x_1470_; size_t v___x_1471_; 
v_node_1469_ = lean_ctor_get(v___x_1463_, 0);
v___x_1470_ = ((size_t)5ULL);
v___x_1471_ = lean_usize_shift_right(v_x_1456_, v___x_1470_);
v_x_1455_ = v_node_1469_;
v_x_1456_ = v___x_1471_;
goto _start;
}
default: 
{
lean_object* v___x_1473_; 
v___x_1473_ = lean_box(0);
return v___x_1473_;
}
}
}
else
{
lean_object* v_ks_1474_; lean_object* v_vs_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v_ks_1474_ = lean_ctor_get(v_x_1455_, 0);
v_vs_1475_ = lean_ctor_get(v_x_1455_, 1);
v___x_1476_ = lean_unsigned_to_nat(0u);
v___x_1477_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1474_, v_vs_1475_, v___x_1476_, v_x_1457_);
return v___x_1477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1478_, lean_object* v_x_1479_, lean_object* v_x_1480_){
_start:
{
size_t v_x_450__boxed_1481_; lean_object* v_res_1482_; 
v_x_450__boxed_1481_ = lean_unbox_usize(v_x_1479_);
lean_dec(v_x_1479_);
v_res_1482_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg(v_x_1478_, v_x_450__boxed_1481_, v_x_1480_);
lean_dec(v_x_1480_);
lean_dec_ref(v_x_1478_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(lean_object* v_x_1483_, lean_object* v_x_1484_){
_start:
{
uint64_t v___y_1486_; 
if (lean_obj_tag(v_x_1484_) == 0)
{
uint64_t v___x_1489_; 
v___x_1489_ = 1723ULL;
v___y_1486_ = v___x_1489_;
goto v___jp_1485_;
}
else
{
uint64_t v_hash_1490_; 
v_hash_1490_ = lean_ctor_get_uint64(v_x_1484_, sizeof(void*)*2);
v___y_1486_ = v_hash_1490_;
goto v___jp_1485_;
}
v___jp_1485_:
{
size_t v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = lean_uint64_to_usize(v___y_1486_);
v___x_1488_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg(v_x_1483_, v___x_1487_, v_x_1484_);
return v___x_1488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg___boxed(lean_object* v_x_1491_, lean_object* v_x_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v_x_1491_, v_x_1492_);
lean_dec(v_x_1492_);
lean_dec_ref(v_x_1491_);
return v_res_1493_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg(lean_object* v_env_1495_, lean_object* v_ext_1496_, lean_object* v_declName_1497_){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1505_; 
v___x_1498_ = lean_obj_once(&l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg___closed__0, &l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg___closed__0);
v___x_1505_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1495_, v_declName_1497_);
if (lean_obj_tag(v___x_1505_) == 0)
{
goto v___jp_1499_;
}
else
{
lean_object* v_val_1506_; lean_object* v_tmpDecl_1528_; lean_object* v_toSignature_1529_; lean_object* v_value_1530_; uint8_t v_recursive_1531_; lean_object* v_inlineAttr_x3f_1532_; lean_object* v_levelParams_1533_; lean_object* v_type_1534_; lean_object* v_params_1535_; uint8_t v_safe_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; 
v_val_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_val_1506_);
lean_dec_ref_known(v___x_1505_, 1);
v_tmpDecl_1528_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0, &l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0_once, _init_l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0);
v_toSignature_1529_ = lean_ctor_get(v_tmpDecl_1528_, 0);
v_value_1530_ = lean_ctor_get(v_tmpDecl_1528_, 1);
v_recursive_1531_ = lean_ctor_get_uint8(v_tmpDecl_1528_, sizeof(void*)*3);
v_inlineAttr_x3f_1532_ = lean_ctor_get(v_tmpDecl_1528_, 2);
v_levelParams_1533_ = lean_ctor_get(v_toSignature_1529_, 1);
v_type_1534_ = lean_ctor_get(v_toSignature_1529_, 2);
v_params_1535_ = lean_ctor_get(v_toSignature_1529_, 3);
v_safe_1536_ = lean_ctor_get_uint8(v_toSignature_1529_, sizeof(void*)*4);
v___x_1537_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_1498_, v_ext_1496_, v_env_1495_, v_val_1506_);
v___x_1538_ = lean_unsigned_to_nat(0u);
v___x_1539_ = lean_array_get_size(v___x_1537_);
v___x_1540_ = lean_nat_dec_lt(v___x_1538_, v___x_1539_);
if (v___x_1540_ == 0)
{
lean_dec_ref(v___x_1537_);
goto v___jp_1507_;
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v___x_1541_ = lean_unsigned_to_nat(1u);
v___x_1542_ = lean_nat_sub(v___x_1539_, v___x_1541_);
v___x_1543_ = lean_nat_dec_le(v___x_1538_, v___x_1542_);
if (v___x_1543_ == 0)
{
lean_dec(v___x_1542_);
lean_dec_ref(v___x_1537_);
goto v___jp_1507_;
}
else
{
lean_object* v___x_1544_; lean_object* v_tmpDecl_1545_; lean_object* v___x_1546_; 
lean_inc_ref(v_params_1535_);
lean_inc_ref(v_type_1534_);
lean_inc(v_levelParams_1533_);
lean_inc(v_declName_1497_);
v___x_1544_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1544_, 0, v_declName_1497_);
lean_ctor_set(v___x_1544_, 1, v_levelParams_1533_);
lean_ctor_set(v___x_1544_, 2, v_type_1534_);
lean_ctor_set(v___x_1544_, 3, v_params_1535_);
lean_ctor_set_uint8(v___x_1544_, sizeof(void*)*4, v_safe_1536_);
lean_inc(v_inlineAttr_x3f_1532_);
lean_inc_ref(v_value_1530_);
v_tmpDecl_1545_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_tmpDecl_1545_, 0, v___x_1544_);
lean_ctor_set(v_tmpDecl_1545_, 1, v_value_1530_);
lean_ctor_set(v_tmpDecl_1545_, 2, v_inlineAttr_x3f_1532_);
lean_ctor_set_uint8(v_tmpDecl_1545_, sizeof(void*)*3, v_recursive_1531_);
v___x_1546_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(v___x_1537_, v_tmpDecl_1545_, v___x_1538_, v___x_1542_);
lean_dec_ref_known(v_tmpDecl_1545_, 3);
lean_dec_ref(v___x_1537_);
if (lean_obj_tag(v___x_1546_) == 0)
{
goto v___jp_1507_;
}
else
{
lean_dec(v_val_1506_);
lean_dec(v_declName_1497_);
lean_dec_ref(v_env_1495_);
return v___x_1546_;
}
}
}
v___jp_1507_:
{
lean_object* v_tmpDecl_1508_; lean_object* v_toSignature_1509_; lean_object* v_value_1510_; uint8_t v_recursive_1511_; lean_object* v_inlineAttr_x3f_1512_; lean_object* v_levelParams_1513_; lean_object* v_type_1514_; lean_object* v_params_1515_; uint8_t v_safe_1516_; uint8_t v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; 
v_tmpDecl_1508_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0, &l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0_once, _init_l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0);
v_toSignature_1509_ = lean_ctor_get(v_tmpDecl_1508_, 0);
v_value_1510_ = lean_ctor_get(v_tmpDecl_1508_, 1);
v_recursive_1511_ = lean_ctor_get_uint8(v_tmpDecl_1508_, sizeof(void*)*3);
v_inlineAttr_x3f_1512_ = lean_ctor_get(v_tmpDecl_1508_, 2);
v_levelParams_1513_ = lean_ctor_get(v_toSignature_1509_, 1);
v_type_1514_ = lean_ctor_get(v_toSignature_1509_, 2);
v_params_1515_ = lean_ctor_get(v_toSignature_1509_, 3);
v_safe_1516_ = lean_ctor_get_uint8(v_toSignature_1509_, sizeof(void*)*4);
v___x_1517_ = 0;
v___x_1518_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1498_, v_ext_1496_, v_env_1495_, v_val_1506_, v___x_1517_);
lean_dec(v_val_1506_);
v___x_1519_ = lean_unsigned_to_nat(0u);
v___x_1520_ = lean_array_get_size(v___x_1518_);
v___x_1521_ = lean_nat_dec_lt(v___x_1519_, v___x_1520_);
if (v___x_1521_ == 0)
{
lean_dec_ref(v___x_1518_);
goto v___jp_1499_;
}
else
{
lean_object* v___x_1522_; lean_object* v___x_1523_; uint8_t v___x_1524_; 
v___x_1522_ = lean_unsigned_to_nat(1u);
v___x_1523_ = lean_nat_sub(v___x_1520_, v___x_1522_);
v___x_1524_ = lean_nat_dec_le(v___x_1519_, v___x_1523_);
if (v___x_1524_ == 0)
{
lean_dec(v___x_1523_);
lean_dec_ref(v___x_1518_);
goto v___jp_1499_;
}
else
{
lean_object* v___x_1525_; lean_object* v_tmpDecl_1526_; lean_object* v___x_1527_; 
lean_inc_ref(v_params_1515_);
lean_inc_ref(v_type_1514_);
lean_inc(v_levelParams_1513_);
lean_inc(v_declName_1497_);
v___x_1525_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1525_, 0, v_declName_1497_);
lean_ctor_set(v___x_1525_, 1, v_levelParams_1513_);
lean_ctor_set(v___x_1525_, 2, v_type_1514_);
lean_ctor_set(v___x_1525_, 3, v_params_1515_);
lean_ctor_set_uint8(v___x_1525_, sizeof(void*)*4, v_safe_1516_);
lean_inc(v_inlineAttr_x3f_1512_);
lean_inc_ref(v_value_1510_);
v_tmpDecl_1526_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_tmpDecl_1526_, 0, v___x_1525_);
lean_ctor_set(v_tmpDecl_1526_, 1, v_value_1510_);
lean_ctor_set(v_tmpDecl_1526_, 2, v_inlineAttr_x3f_1512_);
lean_ctor_set_uint8(v_tmpDecl_1526_, sizeof(void*)*3, v_recursive_1511_);
v___x_1527_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(v___x_1518_, v_tmpDecl_1526_, v___x_1519_, v___x_1523_);
lean_dec_ref_known(v_tmpDecl_1526_, 3);
lean_dec_ref(v___x_1518_);
if (lean_obj_tag(v___x_1527_) == 0)
{
goto v___jp_1499_;
}
else
{
lean_dec(v_declName_1497_);
lean_dec_ref(v_env_1495_);
return v___x_1527_;
}
}
}
}
}
v___jp_1499_:
{
lean_object* v_toEnvExtension_1500_; lean_object* v_asyncMode_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v_toEnvExtension_1500_ = lean_ctor_get(v_ext_1496_, 0);
v_asyncMode_1501_ = lean_ctor_get(v_toEnvExtension_1500_, 2);
v___x_1502_ = lean_box(0);
v___x_1503_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1498_, v_ext_1496_, v_env_1495_, v_asyncMode_1501_, v___x_1502_);
v___x_1504_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_1503_, v_declName_1497_);
lean_dec(v_declName_1497_);
lean_dec(v___x_1503_);
return v___x_1504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg___boxed(lean_object* v_env_1547_, lean_object* v_ext_1548_, lean_object* v_declName_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg(v_env_1547_, v_ext_1548_, v_declName_1549_);
lean_dec_ref(v_ext_1548_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclCore_x3f(uint8_t v_pu_1551_, lean_object* v_env_1552_, lean_object* v_ext_1553_, lean_object* v_declName_1554_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg(v_env_1552_, v_ext_1553_, v_declName_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclCore_x3f___boxed(lean_object* v_pu_1556_, lean_object* v_env_1557_, lean_object* v_ext_1558_, lean_object* v_declName_1559_){
_start:
{
uint8_t v_pu_boxed_1560_; lean_object* v_res_1561_; 
v_pu_boxed_1560_ = lean_unbox(v_pu_1556_);
v_res_1561_ = l_Lean_Compiler_LCNF_getDeclCore_x3f(v_pu_boxed_1560_, v_env_1557_, v_ext_1558_, v_declName_1559_);
lean_dec_ref(v_ext_1558_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0(lean_object* v_00_u03b2_1562_, lean_object* v_x_1563_, lean_object* v_x_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v_x_1563_, v_x_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___boxed(lean_object* v_00_u03b2_1566_, lean_object* v_x_1567_, lean_object* v_x_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0(v_00_u03b2_1566_, v_x_1567_, v_x_1568_);
lean_dec(v_x_1568_);
lean_dec_ref(v_x_1567_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1(lean_object* v_as_1570_, lean_object* v_k_1571_, lean_object* v_x_1572_, lean_object* v_x_1573_, lean_object* v_x_1574_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(v_as_1570_, v_k_1571_, v_x_1572_, v_x_1573_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___boxed(lean_object* v_as_1576_, lean_object* v_k_1577_, lean_object* v_x_1578_, lean_object* v_x_1579_, lean_object* v_x_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1(v_as_1576_, v_k_1577_, v_x_1578_, v_x_1579_, v_x_1580_);
lean_dec_ref(v_k_1577_);
lean_dec_ref(v_as_1576_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1582_, lean_object* v_x_1583_, size_t v_x_1584_, lean_object* v_x_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg(v_x_1583_, v_x_1584_, v_x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1587_, lean_object* v_x_1588_, lean_object* v_x_1589_, lean_object* v_x_1590_){
_start:
{
size_t v_x_593__boxed_1591_; lean_object* v_res_1592_; 
v_x_593__boxed_1591_ = lean_unbox_usize(v_x_1589_);
lean_dec(v_x_1589_);
v_res_1592_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0(v_00_u03b2_1587_, v_x_1588_, v_x_593__boxed_1591_, v_x_1590_);
lean_dec(v_x_1590_);
lean_dec_ref(v_x_1588_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1593_, lean_object* v_keys_1594_, lean_object* v_vals_1595_, lean_object* v_heq_1596_, lean_object* v_i_1597_, lean_object* v_k_1598_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1594_, v_vals_1595_, v_i_1597_, v_k_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1600_, lean_object* v_keys_1601_, lean_object* v_vals_1602_, lean_object* v_heq_1603_, lean_object* v_i_1604_, lean_object* v_k_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1600_, v_keys_1601_, v_vals_1602_, v_heq_1603_, v_i_1604_, v_k_1605_);
lean_dec(v_k_1605_);
lean_dec_ref(v_vals_1602_);
lean_dec_ref(v_keys_1601_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(lean_object* v_as_1607_, lean_object* v_k_1608_, lean_object* v_x_1609_, lean_object* v_x_1610_){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v_m_1613_; lean_object* v_a_1614_; uint8_t v___x_1615_; 
v___x_1611_ = lean_nat_add(v_x_1609_, v_x_1610_);
v___x_1612_ = lean_unsigned_to_nat(1u);
v_m_1613_ = lean_nat_shiftr(v___x_1611_, v___x_1612_);
lean_dec(v___x_1611_);
v_a_1614_ = lean_array_fget_borrowed(v_as_1607_, v_m_1613_);
v___x_1615_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2(v_a_1614_, v_k_1608_);
if (v___x_1615_ == 0)
{
uint8_t v___x_1616_; 
lean_dec(v_x_1610_);
v___x_1616_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2(v_k_1608_, v_a_1614_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; 
lean_dec(v_m_1613_);
lean_dec(v_x_1609_);
lean_inc(v_a_1614_);
v___x_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1617_, 0, v_a_1614_);
return v___x_1617_;
}
else
{
lean_object* v___x_1618_; uint8_t v___x_1619_; lean_object* v___x_1620_; uint8_t v___y_1622_; 
v___x_1618_ = lean_unsigned_to_nat(0u);
v___x_1619_ = lean_nat_dec_eq(v_m_1613_, v___x_1618_);
v___x_1620_ = lean_nat_sub(v_m_1613_, v___x_1612_);
lean_dec(v_m_1613_);
if (v___x_1619_ == 0)
{
uint8_t v___x_1625_; 
v___x_1625_ = lean_nat_dec_lt(v___x_1620_, v_x_1609_);
v___y_1622_ = v___x_1625_;
goto v___jp_1621_;
}
else
{
v___y_1622_ = v___x_1619_;
goto v___jp_1621_;
}
v___jp_1621_:
{
if (v___y_1622_ == 0)
{
v_x_1610_ = v___x_1620_;
goto _start;
}
else
{
lean_object* v___x_1624_; 
lean_dec(v___x_1620_);
lean_dec(v_x_1609_);
v___x_1624_ = lean_box(0);
return v___x_1624_;
}
}
}
}
else
{
lean_object* v___x_1626_; uint8_t v___x_1627_; 
lean_dec(v_x_1609_);
v___x_1626_ = lean_nat_add(v_m_1613_, v___x_1612_);
lean_dec(v_m_1613_);
v___x_1627_ = lean_nat_dec_le(v___x_1626_, v_x_1610_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; 
lean_dec(v___x_1626_);
lean_dec(v_x_1610_);
v___x_1628_ = lean_box(0);
return v___x_1628_;
}
else
{
v_x_1609_ = v___x_1626_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg___boxed(lean_object* v_as_1630_, lean_object* v_k_1631_, lean_object* v_x_1632_, lean_object* v_x_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(v_as_1630_, v_k_1631_, v_x_1632_, v_x_1633_);
lean_dec_ref(v_k_1631_);
lean_dec_ref(v_as_1630_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSigCore_x3f___redArg(lean_object* v_env_1635_, lean_object* v_ext_1636_, lean_object* v_declName_1637_){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1645_; 
v___x_1638_ = lean_obj_once(&l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg___closed__0, &l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg___closed__0);
v___x_1645_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1635_, v_declName_1637_);
if (lean_obj_tag(v___x_1645_) == 0)
{
goto v___jp_1639_;
}
else
{
lean_object* v_val_1646_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; uint8_t v___x_1666_; 
v_val_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_val_1646_);
lean_dec_ref_known(v___x_1645_, 1);
v___x_1663_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_1638_, v_ext_1636_, v_env_1635_, v_val_1646_);
v___x_1664_ = lean_unsigned_to_nat(0u);
v___x_1665_ = lean_array_get_size(v___x_1663_);
v___x_1666_ = lean_nat_dec_lt(v___x_1664_, v___x_1665_);
if (v___x_1666_ == 0)
{
lean_dec_ref(v___x_1663_);
goto v___jp_1647_;
}
else
{
lean_object* v_tmpSig_1667_; lean_object* v_levelParams_1668_; lean_object* v_type_1669_; lean_object* v_params_1670_; uint8_t v_safe_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; uint8_t v___x_1674_; 
v_tmpSig_1667_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0, &l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0_once, _init_l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0);
v_levelParams_1668_ = lean_ctor_get(v_tmpSig_1667_, 1);
v_type_1669_ = lean_ctor_get(v_tmpSig_1667_, 2);
v_params_1670_ = lean_ctor_get(v_tmpSig_1667_, 3);
v_safe_1671_ = lean_ctor_get_uint8(v_tmpSig_1667_, sizeof(void*)*4);
v___x_1672_ = lean_unsigned_to_nat(1u);
v___x_1673_ = lean_nat_sub(v___x_1665_, v___x_1672_);
v___x_1674_ = lean_nat_dec_le(v___x_1664_, v___x_1673_);
if (v___x_1674_ == 0)
{
lean_dec(v___x_1673_);
lean_dec_ref(v___x_1663_);
goto v___jp_1647_;
}
else
{
lean_object* v_tmpSig_1675_; lean_object* v___x_1676_; 
lean_inc_ref(v_params_1670_);
lean_inc_ref(v_type_1669_);
lean_inc(v_levelParams_1668_);
lean_inc(v_declName_1637_);
v_tmpSig_1675_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_tmpSig_1675_, 0, v_declName_1637_);
lean_ctor_set(v_tmpSig_1675_, 1, v_levelParams_1668_);
lean_ctor_set(v_tmpSig_1675_, 2, v_type_1669_);
lean_ctor_set(v_tmpSig_1675_, 3, v_params_1670_);
lean_ctor_set_uint8(v_tmpSig_1675_, sizeof(void*)*4, v_safe_1671_);
v___x_1676_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(v___x_1663_, v_tmpSig_1675_, v___x_1664_, v___x_1673_);
lean_dec_ref_known(v_tmpSig_1675_, 4);
lean_dec_ref(v___x_1663_);
if (lean_obj_tag(v___x_1676_) == 0)
{
goto v___jp_1647_;
}
else
{
lean_dec(v_val_1646_);
lean_dec(v_declName_1637_);
lean_dec_ref(v_env_1635_);
return v___x_1676_;
}
}
}
v___jp_1647_:
{
uint8_t v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; uint8_t v___x_1652_; 
v___x_1648_ = 0;
v___x_1649_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1638_, v_ext_1636_, v_env_1635_, v_val_1646_, v___x_1648_);
lean_dec(v_val_1646_);
v___x_1650_ = lean_unsigned_to_nat(0u);
v___x_1651_ = lean_array_get_size(v___x_1649_);
v___x_1652_ = lean_nat_dec_lt(v___x_1650_, v___x_1651_);
if (v___x_1652_ == 0)
{
lean_dec_ref(v___x_1649_);
goto v___jp_1639_;
}
else
{
lean_object* v_tmpSig_1653_; lean_object* v_levelParams_1654_; lean_object* v_type_1655_; lean_object* v_params_1656_; uint8_t v_safe_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; uint8_t v___x_1660_; 
v_tmpSig_1653_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0, &l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0_once, _init_l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0);
v_levelParams_1654_ = lean_ctor_get(v_tmpSig_1653_, 1);
v_type_1655_ = lean_ctor_get(v_tmpSig_1653_, 2);
v_params_1656_ = lean_ctor_get(v_tmpSig_1653_, 3);
v_safe_1657_ = lean_ctor_get_uint8(v_tmpSig_1653_, sizeof(void*)*4);
v___x_1658_ = lean_unsigned_to_nat(1u);
v___x_1659_ = lean_nat_sub(v___x_1651_, v___x_1658_);
v___x_1660_ = lean_nat_dec_le(v___x_1650_, v___x_1659_);
if (v___x_1660_ == 0)
{
lean_dec(v___x_1659_);
lean_dec_ref(v___x_1649_);
goto v___jp_1639_;
}
else
{
lean_object* v_tmpSig_1661_; lean_object* v___x_1662_; 
lean_inc_ref(v_params_1656_);
lean_inc_ref(v_type_1655_);
lean_inc(v_levelParams_1654_);
lean_inc(v_declName_1637_);
v_tmpSig_1661_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_tmpSig_1661_, 0, v_declName_1637_);
lean_ctor_set(v_tmpSig_1661_, 1, v_levelParams_1654_);
lean_ctor_set(v_tmpSig_1661_, 2, v_type_1655_);
lean_ctor_set(v_tmpSig_1661_, 3, v_params_1656_);
lean_ctor_set_uint8(v_tmpSig_1661_, sizeof(void*)*4, v_safe_1657_);
v___x_1662_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(v___x_1649_, v_tmpSig_1661_, v___x_1650_, v___x_1659_);
lean_dec_ref_known(v_tmpSig_1661_, 4);
lean_dec_ref(v___x_1649_);
if (lean_obj_tag(v___x_1662_) == 0)
{
goto v___jp_1639_;
}
else
{
lean_dec(v_declName_1637_);
lean_dec_ref(v_env_1635_);
return v___x_1662_;
}
}
}
}
}
v___jp_1639_:
{
lean_object* v_toEnvExtension_1640_; lean_object* v_asyncMode_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_toEnvExtension_1640_ = lean_ctor_get(v_ext_1636_, 0);
v_asyncMode_1641_ = lean_ctor_get(v_toEnvExtension_1640_, 2);
v___x_1642_ = lean_box(0);
v___x_1643_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1638_, v_ext_1636_, v_env_1635_, v_asyncMode_1641_, v___x_1642_);
v___x_1644_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_1643_, v_declName_1637_);
lean_dec(v_declName_1637_);
lean_dec(v___x_1643_);
return v___x_1644_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSigCore_x3f___redArg___boxed(lean_object* v_env_1677_, lean_object* v_ext_1678_, lean_object* v_declName_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_Compiler_LCNF_getSigCore_x3f___redArg(v_env_1677_, v_ext_1678_, v_declName_1679_);
lean_dec_ref(v_ext_1678_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSigCore_x3f(uint8_t v_pu_1681_, lean_object* v_env_1682_, lean_object* v_ext_1683_, lean_object* v_declName_1684_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Lean_Compiler_LCNF_getSigCore_x3f___redArg(v_env_1682_, v_ext_1683_, v_declName_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSigCore_x3f___boxed(lean_object* v_pu_1686_, lean_object* v_env_1687_, lean_object* v_ext_1688_, lean_object* v_declName_1689_){
_start:
{
uint8_t v_pu_boxed_1690_; lean_object* v_res_1691_; 
v_pu_boxed_1690_ = lean_unbox(v_pu_1686_);
v_res_1691_ = l_Lean_Compiler_LCNF_getSigCore_x3f(v_pu_boxed_1690_, v_env_1687_, v_ext_1688_, v_declName_1689_);
lean_dec_ref(v_ext_1688_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0(lean_object* v_as_1692_, lean_object* v_k_1693_, lean_object* v_x_1694_, lean_object* v_x_1695_, lean_object* v_x_1696_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(v_as_1692_, v_k_1693_, v_x_1694_, v_x_1695_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___boxed(lean_object* v_as_1698_, lean_object* v_k_1699_, lean_object* v_x_1700_, lean_object* v_x_1701_, lean_object* v_x_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0(v_as_1698_, v_k_1699_, v_x_1700_, v_x_1701_, v_x_1702_);
lean_dec_ref(v_k_1699_);
lean_dec_ref(v_as_1698_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg(lean_object* v_declName_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v___x_1707_; lean_object* v_env_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1707_ = lean_st_ref_get(v_a_1705_);
v_env_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc_ref(v_env_1708_);
lean_dec(v___x_1707_);
v___x_1709_ = l_Lean_Compiler_LCNF_baseExt;
v___x_1710_ = l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg(v_env_1708_, v___x_1709_, v_declName_1704_);
v___x_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg___boxed(lean_object* v_declName_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg(v_declName_1712_, v_a_1713_);
lean_dec(v_a_1713_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBaseDecl_x3f(lean_object* v_declName_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg(v_declName_1716_, v_a_1718_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBaseDecl_x3f___boxed(lean_object* v_declName_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_Compiler_LCNF_getBaseDecl_x3f(v_declName_1721_, v_a_1722_, v_a_1723_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(lean_object* v_declName_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v___x_1729_; lean_object* v_env_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1729_ = lean_st_ref_get(v_a_1727_);
v_env_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc_ref(v_env_1730_);
lean_dec(v___x_1729_);
v___x_1731_ = l_Lean_Compiler_LCNF_monoExt;
v___x_1732_ = l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg(v_env_1730_, v___x_1731_, v_declName_1726_);
v___x_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg___boxed(lean_object* v_declName_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_1734_, v_a_1735_);
lean_dec(v_a_1735_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f(lean_object* v_declName_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_1738_, v_a_1740_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___boxed(lean_object* v_declName_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f(v_declName_1743_, v_a_1744_, v_a_1745_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg(lean_object* v_declName_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v_env_1753_; lean_object* v___x_1754_; lean_object* v_asyncMode_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1751_ = lean_obj_once(&l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg___closed__0, &l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg___closed__0);
v___x_1752_ = lean_st_ref_get(v_a_1749_);
v_env_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc_ref(v_env_1753_);
lean_dec(v___x_1752_);
v___x_1754_ = l_Lean_Compiler_LCNF_impureExt;
v_asyncMode_1755_ = lean_ctor_get(v___x_1754_, 2);
v___x_1756_ = lean_box(0);
v___x_1757_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1751_, v___x_1754_, v_env_1753_, v_asyncMode_1755_, v___x_1756_);
v___x_1758_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_1757_, v_declName_1748_);
lean_dec(v___x_1757_);
v___x_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg___boxed(lean_object* v_declName_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg(v_declName_1760_, v_a_1761_);
lean_dec(v_a_1761_);
lean_dec(v_declName_1760_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f(lean_object* v_declName_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg(v_declName_1764_, v_a_1766_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___boxed(lean_object* v_declName_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f(v_declName_1769_, v_a_1770_, v_a_1771_);
lean_dec(v_a_1771_);
lean_dec_ref(v_a_1770_);
lean_dec(v_declName_1769_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__1(size_t v_sz_1774_, size_t v_i_1775_, lean_object* v_bs_1776_){
_start:
{
uint8_t v___x_1777_; 
v___x_1777_ = lean_usize_dec_lt(v_i_1775_, v_sz_1774_);
if (v___x_1777_ == 0)
{
return v_bs_1776_;
}
else
{
lean_object* v_v_1778_; lean_object* v_fst_1779_; lean_object* v___x_1780_; lean_object* v_bs_x27_1781_; size_t v___x_1782_; size_t v___x_1783_; lean_object* v___x_1784_; 
v_v_1778_ = lean_array_uget_borrowed(v_bs_1776_, v_i_1775_);
v_fst_1779_ = lean_ctor_get(v_v_1778_, 0);
lean_inc(v_fst_1779_);
v___x_1780_ = lean_unsigned_to_nat(0u);
v_bs_x27_1781_ = lean_array_uset(v_bs_1776_, v_i_1775_, v___x_1780_);
v___x_1782_ = ((size_t)1ULL);
v___x_1783_ = lean_usize_add(v_i_1775_, v___x_1782_);
v___x_1784_ = lean_array_uset(v_bs_x27_1781_, v_i_1775_, v_fst_1779_);
v_i_1775_ = v___x_1783_;
v_bs_1776_ = v___x_1784_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__1___boxed(lean_object* v_sz_1786_, lean_object* v_i_1787_, lean_object* v_bs_1788_){
_start:
{
size_t v_sz_boxed_1789_; size_t v_i_boxed_1790_; lean_object* v_res_1791_; 
v_sz_boxed_1789_ = lean_unbox_usize(v_sz_1786_);
lean_dec(v_sz_1786_);
v_i_boxed_1790_ = lean_unbox_usize(v_i_1787_);
lean_dec(v_i_1787_);
v_res_1791_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__1(v_sz_boxed_1789_, v_i_boxed_1790_, v_bs_1788_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___lam__0(lean_object* v_ps_1792_, lean_object* v_k_1793_, lean_object* v_v_1794_){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1795_, 0, v_k_1793_);
lean_ctor_set(v___x_1795_, 1, v_v_1794_);
v___x_1796_ = lean_array_push(v_ps_1792_, v___x_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg(lean_object* v_m_1800_){
_start:
{
lean_object* v___f_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___f_1801_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__0));
v___x_1802_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__1));
v___x_1803_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_m_1800_, v___f_1801_, v___x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___boxed(lean_object* v_m_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg(v_m_1804_);
lean_dec_ref(v_m_1804_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecls___redArg(lean_object* v_a_1806_){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v_env_1810_; lean_object* v___x_1811_; lean_object* v_asyncMode_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; size_t v_sz_1816_; size_t v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1808_ = lean_obj_once(&l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg___closed__0, &l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg___closed__0);
v___x_1809_ = lean_st_ref_get(v_a_1806_);
v_env_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc_ref(v_env_1810_);
lean_dec(v___x_1809_);
v___x_1811_ = l_Lean_Compiler_LCNF_impureExt;
v_asyncMode_1812_ = lean_ctor_get(v___x_1811_, 2);
v___x_1813_ = lean_box(0);
v___x_1814_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1808_, v___x_1811_, v_env_1810_, v_asyncMode_1812_, v___x_1813_);
v___x_1815_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg(v___x_1814_);
lean_dec(v___x_1814_);
v_sz_1816_ = lean_array_size(v___x_1815_);
v___x_1817_ = ((size_t)0ULL);
v___x_1818_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__1(v_sz_1816_, v___x_1817_, v___x_1815_);
v___x_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecls___redArg___boxed(lean_object* v_a_1820_, lean_object* v_a_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_Compiler_LCNF_getLocalImpureDecls___redArg(v_a_1820_);
lean_dec(v_a_1820_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecls(lean_object* v_a_1823_, lean_object* v_a_1824_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Lean_Compiler_LCNF_getLocalImpureDecls___redArg(v_a_1824_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecls___boxed(lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Lean_Compiler_LCNF_getLocalImpureDecls(v_a_1827_, v_a_1828_);
lean_dec(v_a_1828_);
lean_dec_ref(v_a_1827_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0(lean_object* v_00_u03b2_1831_, lean_object* v_m_1832_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg(v_m_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___boxed(lean_object* v_00_u03b2_1834_, lean_object* v_m_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0(v_00_u03b2_1834_, v_m_1835_);
lean_dec_ref(v_m_1835_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object* v_declName_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v___x_1840_; lean_object* v_env_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1840_ = lean_st_ref_get(v_a_1838_);
v_env_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc_ref(v_env_1841_);
lean_dec(v___x_1840_);
v___x_1842_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_1843_ = l_Lean_Compiler_LCNF_getSigCore_x3f___redArg(v_env_1841_, v___x_1842_, v_declName_1837_);
v___x_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg___boxed(lean_object* v_declName_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_1845_, v_a_1846_);
lean_dec(v_a_1846_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f(lean_object* v_declName_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_1849_, v_a_1851_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___boxed(lean_object* v_declName_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f(v_declName_1854_, v_a_1855_, v_a_1856_);
lean_dec(v_a_1856_);
lean_dec_ref(v_a_1855_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveBaseDeclCore(lean_object* v_env_1859_, lean_object* v_decl_1860_){
_start:
{
lean_object* v___x_1861_; lean_object* v_toEnvExtension_1862_; lean_object* v_asyncMode_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1861_ = l_Lean_Compiler_LCNF_baseExt;
v_toEnvExtension_1862_ = lean_ctor_get(v___x_1861_, 0);
v_asyncMode_1863_ = lean_ctor_get(v_toEnvExtension_1862_, 2);
v___x_1864_ = lean_box(0);
v___x_1865_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1861_, v_env_1859_, v_decl_1860_, v_asyncMode_1863_, v___x_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveMonoDeclCore(lean_object* v_env_1866_, lean_object* v_decl_1867_){
_start:
{
lean_object* v___x_1868_; lean_object* v_toEnvExtension_1869_; lean_object* v_asyncMode_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1868_ = l_Lean_Compiler_LCNF_monoExt;
v_toEnvExtension_1869_ = lean_ctor_get(v___x_1868_, 0);
v_asyncMode_1870_ = lean_ctor_get(v_toEnvExtension_1869_, 2);
v___x_1871_ = lean_box(0);
v___x_1872_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1868_, v_env_1866_, v_decl_1867_, v_asyncMode_1870_, v___x_1871_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveImpureDeclCore___lam__0(lean_object* v_toSignature_1873_, lean_object* v_decl_1874_, lean_object* v_s_1875_){
_start:
{
lean_object* v_name_1876_; lean_object* v___x_1877_; 
v_name_1876_ = lean_ctor_get(v_toSignature_1873_, 0);
lean_inc(v_name_1876_);
lean_dec_ref(v_toSignature_1873_);
v___x_1877_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_s_1875_, v_name_1876_, v_decl_1874_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveImpureDeclCore(lean_object* v_env_1878_, lean_object* v_decl_1879_){
_start:
{
lean_object* v___x_1880_; lean_object* v_asyncMode_1881_; lean_object* v_toSignature_1882_; lean_object* v___x_1883_; lean_object* v_toEnvExtension_1884_; lean_object* v_asyncMode_1885_; lean_object* v___f_1886_; lean_object* v___x_1887_; lean_object* v_env_1888_; lean_object* v___x_1889_; 
v___x_1880_ = l_Lean_Compiler_LCNF_impureExt;
v_asyncMode_1881_ = lean_ctor_get(v___x_1880_, 2);
v_toSignature_1882_ = lean_ctor_get(v_decl_1879_, 0);
lean_inc_ref_n(v_toSignature_1882_, 2);
v___x_1883_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_1884_ = lean_ctor_get(v___x_1883_, 0);
v_asyncMode_1885_ = lean_ctor_get(v_toEnvExtension_1884_, 2);
v___f_1886_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_saveImpureDeclCore___lam__0), 3, 2);
lean_closure_set(v___f_1886_, 0, v_toSignature_1882_);
lean_closure_set(v___f_1886_, 1, v_decl_1879_);
v___x_1887_ = lean_box(0);
v_env_1888_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1880_, v_env_1878_, v___f_1886_, v_asyncMode_1881_, v___x_1887_);
v___x_1889_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1883_, v_env_1888_, v_toSignature_1882_, v_asyncMode_1885_, v___x_1887_);
return v___x_1889_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0(void){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__3, &l_Lean_Compiler_LCNF_mkDeclExt___closed__3_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__3);
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
return v___x_1891_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0, &l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0);
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___redArg(lean_object* v_decl_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v___x_1897_; lean_object* v_env_1898_; lean_object* v_nextMacroScope_1899_; lean_object* v_ngen_1900_; lean_object* v_auxDeclNGen_1901_; lean_object* v_traceState_1902_; lean_object* v_messages_1903_; lean_object* v_infoState_1904_; lean_object* v_snapshotTasks_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1917_; 
v___x_1897_ = lean_st_ref_take(v_a_1895_);
v_env_1898_ = lean_ctor_get(v___x_1897_, 0);
v_nextMacroScope_1899_ = lean_ctor_get(v___x_1897_, 1);
v_ngen_1900_ = lean_ctor_get(v___x_1897_, 2);
v_auxDeclNGen_1901_ = lean_ctor_get(v___x_1897_, 3);
v_traceState_1902_ = lean_ctor_get(v___x_1897_, 4);
v_messages_1903_ = lean_ctor_get(v___x_1897_, 6);
v_infoState_1904_ = lean_ctor_get(v___x_1897_, 7);
v_snapshotTasks_1905_ = lean_ctor_get(v___x_1897_, 8);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1917_ == 0)
{
lean_object* v_unused_1918_; 
v_unused_1918_ = lean_ctor_get(v___x_1897_, 5);
lean_dec(v_unused_1918_);
v___x_1907_ = v___x_1897_;
v_isShared_1908_ = v_isSharedCheck_1917_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_snapshotTasks_1905_);
lean_inc(v_infoState_1904_);
lean_inc(v_messages_1903_);
lean_inc(v_traceState_1902_);
lean_inc(v_auxDeclNGen_1901_);
lean_inc(v_ngen_1900_);
lean_inc(v_nextMacroScope_1899_);
lean_inc(v_env_1898_);
lean_dec(v___x_1897_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1917_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1909_ = lean_box(0);
v___x_1910_ = l_Lean_Compiler_LCNF_saveBaseDeclCore(v_env_1898_, v_decl_1894_);
v___x_1911_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1, &l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 5, v___x_1911_);
lean_ctor_set(v___x_1907_, 0, v___x_1910_);
v___x_1913_ = v___x_1907_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1910_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v_nextMacroScope_1899_);
lean_ctor_set(v_reuseFailAlloc_1916_, 2, v_ngen_1900_);
lean_ctor_set(v_reuseFailAlloc_1916_, 3, v_auxDeclNGen_1901_);
lean_ctor_set(v_reuseFailAlloc_1916_, 4, v_traceState_1902_);
lean_ctor_set(v_reuseFailAlloc_1916_, 5, v___x_1911_);
lean_ctor_set(v_reuseFailAlloc_1916_, 6, v_messages_1903_);
lean_ctor_set(v_reuseFailAlloc_1916_, 7, v_infoState_1904_);
lean_ctor_set(v_reuseFailAlloc_1916_, 8, v_snapshotTasks_1905_);
v___x_1913_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = lean_st_ref_put(v_a_1895_, v___x_1913_);
v___x_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1909_);
return v___x_1915_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___redArg___boxed(lean_object* v_decl_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(v_decl_1919_, v_a_1920_);
lean_dec(v_a_1920_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveBase(lean_object* v_decl_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(v_decl_1923_, v_a_1925_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___boxed(lean_object* v_decl_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lean_Compiler_LCNF_Decl_saveBase(v_decl_1928_, v_a_1929_, v_a_1930_);
lean_dec(v_a_1930_);
lean_dec_ref(v_a_1929_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg(lean_object* v_decl_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v___x_1936_; lean_object* v_env_1937_; lean_object* v_nextMacroScope_1938_; lean_object* v_ngen_1939_; lean_object* v_auxDeclNGen_1940_; lean_object* v_traceState_1941_; lean_object* v_messages_1942_; lean_object* v_infoState_1943_; lean_object* v_snapshotTasks_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1956_; 
v___x_1936_ = lean_st_ref_take(v_a_1934_);
v_env_1937_ = lean_ctor_get(v___x_1936_, 0);
v_nextMacroScope_1938_ = lean_ctor_get(v___x_1936_, 1);
v_ngen_1939_ = lean_ctor_get(v___x_1936_, 2);
v_auxDeclNGen_1940_ = lean_ctor_get(v___x_1936_, 3);
v_traceState_1941_ = lean_ctor_get(v___x_1936_, 4);
v_messages_1942_ = lean_ctor_get(v___x_1936_, 6);
v_infoState_1943_ = lean_ctor_get(v___x_1936_, 7);
v_snapshotTasks_1944_ = lean_ctor_get(v___x_1936_, 8);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1956_ == 0)
{
lean_object* v_unused_1957_; 
v_unused_1957_ = lean_ctor_get(v___x_1936_, 5);
lean_dec(v_unused_1957_);
v___x_1946_ = v___x_1936_;
v_isShared_1947_ = v_isSharedCheck_1956_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_snapshotTasks_1944_);
lean_inc(v_infoState_1943_);
lean_inc(v_messages_1942_);
lean_inc(v_traceState_1941_);
lean_inc(v_auxDeclNGen_1940_);
lean_inc(v_ngen_1939_);
lean_inc(v_nextMacroScope_1938_);
lean_inc(v_env_1937_);
lean_dec(v___x_1936_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1956_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1952_; 
v___x_1948_ = lean_box(0);
v___x_1949_ = l_Lean_Compiler_LCNF_saveMonoDeclCore(v_env_1937_, v_decl_1933_);
v___x_1950_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1, &l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 5, v___x_1950_);
lean_ctor_set(v___x_1946_, 0, v___x_1949_);
v___x_1952_ = v___x_1946_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1949_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_nextMacroScope_1938_);
lean_ctor_set(v_reuseFailAlloc_1955_, 2, v_ngen_1939_);
lean_ctor_set(v_reuseFailAlloc_1955_, 3, v_auxDeclNGen_1940_);
lean_ctor_set(v_reuseFailAlloc_1955_, 4, v_traceState_1941_);
lean_ctor_set(v_reuseFailAlloc_1955_, 5, v___x_1950_);
lean_ctor_set(v_reuseFailAlloc_1955_, 6, v_messages_1942_);
lean_ctor_set(v_reuseFailAlloc_1955_, 7, v_infoState_1943_);
lean_ctor_set(v_reuseFailAlloc_1955_, 8, v_snapshotTasks_1944_);
v___x_1952_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = lean_st_ref_put(v_a_1934_, v___x_1952_);
v___x_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1948_);
return v___x_1954_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg___boxed(lean_object* v_decl_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v_decl_1958_, v_a_1959_);
lean_dec(v_a_1959_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveMono(lean_object* v_decl_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_){
_start:
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v_decl_1962_, v_a_1964_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___boxed(lean_object* v_decl_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Lean_Compiler_LCNF_Decl_saveMono(v_decl_1967_, v_a_1968_, v_a_1969_);
lean_dec(v_a_1969_);
lean_dec_ref(v_a_1968_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(lean_object* v_decl_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v___x_1975_; lean_object* v_env_1976_; lean_object* v_nextMacroScope_1977_; lean_object* v_ngen_1978_; lean_object* v_auxDeclNGen_1979_; lean_object* v_traceState_1980_; lean_object* v_messages_1981_; lean_object* v_infoState_1982_; lean_object* v_snapshotTasks_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1995_; 
v___x_1975_ = lean_st_ref_take(v_a_1973_);
v_env_1976_ = lean_ctor_get(v___x_1975_, 0);
v_nextMacroScope_1977_ = lean_ctor_get(v___x_1975_, 1);
v_ngen_1978_ = lean_ctor_get(v___x_1975_, 2);
v_auxDeclNGen_1979_ = lean_ctor_get(v___x_1975_, 3);
v_traceState_1980_ = lean_ctor_get(v___x_1975_, 4);
v_messages_1981_ = lean_ctor_get(v___x_1975_, 6);
v_infoState_1982_ = lean_ctor_get(v___x_1975_, 7);
v_snapshotTasks_1983_ = lean_ctor_get(v___x_1975_, 8);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; 
v_unused_1996_ = lean_ctor_get(v___x_1975_, 5);
lean_dec(v_unused_1996_);
v___x_1985_ = v___x_1975_;
v_isShared_1986_ = v_isSharedCheck_1995_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_snapshotTasks_1983_);
lean_inc(v_infoState_1982_);
lean_inc(v_messages_1981_);
lean_inc(v_traceState_1980_);
lean_inc(v_auxDeclNGen_1979_);
lean_inc(v_ngen_1978_);
lean_inc(v_nextMacroScope_1977_);
lean_inc(v_env_1976_);
lean_dec(v___x_1975_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1995_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1991_; 
v___x_1987_ = lean_box(0);
v___x_1988_ = l_Lean_Compiler_LCNF_saveImpureDeclCore(v_env_1976_, v_decl_1972_);
v___x_1989_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1, &l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 5, v___x_1989_);
lean_ctor_set(v___x_1985_, 0, v___x_1988_);
v___x_1991_ = v___x_1985_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_nextMacroScope_1977_);
lean_ctor_set(v_reuseFailAlloc_1994_, 2, v_ngen_1978_);
lean_ctor_set(v_reuseFailAlloc_1994_, 3, v_auxDeclNGen_1979_);
lean_ctor_set(v_reuseFailAlloc_1994_, 4, v_traceState_1980_);
lean_ctor_set(v_reuseFailAlloc_1994_, 5, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_1994_, 6, v_messages_1981_);
lean_ctor_set(v_reuseFailAlloc_1994_, 7, v_infoState_1982_);
lean_ctor_set(v_reuseFailAlloc_1994_, 8, v_snapshotTasks_1983_);
v___x_1991_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = lean_st_ref_put(v_a_1973_, v___x_1991_);
v___x_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1987_);
return v___x_1993_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___redArg___boxed(lean_object* v_decl_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_decl_1997_, v_a_1998_);
lean_dec(v_a_1998_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure(lean_object* v_decl_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_){
_start:
{
lean_object* v___x_2005_; 
v___x_2005_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_decl_2001_, v_a_2003_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___boxed(lean_object* v_decl_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Lean_Compiler_LCNF_Decl_saveImpure(v_decl_2006_, v_a_2007_, v_a_2008_);
lean_dec(v_a_2008_);
lean_dec_ref(v_a_2007_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__0(lean_object* v_decl_2011_, lean_object* v_h_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(v_decl_2011_, v___y_2016_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__0___boxed(lean_object* v_decl_2019_, lean_object* v_h_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_Compiler_LCNF_Decl_save___lam__0(v_decl_2019_, v_h_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__1(lean_object* v_decl_2027_, lean_object* v_h_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v_decl_2027_, v___y_2032_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__1___boxed(lean_object* v_decl_2035_, lean_object* v_h_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_Lean_Compiler_LCNF_Decl_save___lam__1(v_decl_2035_, v_h_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__2(lean_object* v_decl_2043_, lean_object* v_h_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_decl_2043_, v___y_2048_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__2___boxed(lean_object* v_decl_2051_, lean_object* v_h_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Lean_Compiler_LCNF_Decl_save___lam__2(v_decl_2051_, v_h_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
return v_res_2058_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_save___closed__0(void){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_instMonadEIO___redArg();
return v___x_2059_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_save___closed__1(void){
_start:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_save___closed__0, &l_Lean_Compiler_LCNF_Decl_save___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_save___closed__0);
v___x_2061_ = l_StateRefT_x27_instMonad___redArg(v___x_2060_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save(uint8_t v_pu_2064_, lean_object* v_decl_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_){
_start:
{
lean_object* v___x_2071_; lean_object* v_toApplicative_2072_; lean_object* v_toFunctor_2073_; lean_object* v_toSeq_2074_; lean_object* v_toSeqLeft_2075_; lean_object* v_toSeqRight_2076_; lean_object* v___f_2077_; lean_object* v___f_2078_; lean_object* v___f_2079_; lean_object* v___f_2080_; lean_object* v___f_2081_; lean_object* v___f_2082_; lean_object* v___f_2083_; lean_object* v___x_2084_; lean_object* v___f_2085_; lean_object* v___f_2086_; lean_object* v___f_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___f_2093_; lean_object* v___x_2094_; 
v___x_2071_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_save___closed__1, &l_Lean_Compiler_LCNF_Decl_save___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_save___closed__1);
v_toApplicative_2072_ = lean_ctor_get(v___x_2071_, 0);
v_toFunctor_2073_ = lean_ctor_get(v_toApplicative_2072_, 0);
v_toSeq_2074_ = lean_ctor_get(v_toApplicative_2072_, 2);
v_toSeqLeft_2075_ = lean_ctor_get(v_toApplicative_2072_, 3);
v_toSeqRight_2076_ = lean_ctor_get(v_toApplicative_2072_, 4);
lean_inc_ref_n(v_decl_2065_, 2);
v___f_2077_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_save___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2077_, 0, v_decl_2065_);
v___f_2078_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_save___lam__1___boxed), 7, 1);
lean_closure_set(v___f_2078_, 0, v_decl_2065_);
v___f_2079_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_save___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2079_, 0, v_decl_2065_);
v___f_2080_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_save___closed__2));
v___f_2081_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_save___closed__3));
lean_inc_ref_n(v_toFunctor_2073_, 2);
v___f_2082_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2082_, 0, v_toFunctor_2073_);
v___f_2083_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2083_, 0, v_toFunctor_2073_);
v___x_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___f_2082_);
lean_ctor_set(v___x_2084_, 1, v___f_2083_);
lean_inc(v_toSeqRight_2076_);
v___f_2085_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2085_, 0, v_toSeqRight_2076_);
lean_inc(v_toSeqLeft_2075_);
v___f_2086_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2086_, 0, v_toSeqLeft_2075_);
lean_inc(v_toSeq_2074_);
v___f_2087_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2087_, 0, v_toSeq_2074_);
v___x_2088_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2084_);
lean_ctor_set(v___x_2088_, 1, v___f_2080_);
lean_ctor_set(v___x_2088_, 2, v___f_2087_);
lean_ctor_set(v___x_2088_, 3, v___f_2086_);
lean_ctor_set(v___x_2088_, 4, v___f_2085_);
v___x_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
lean_ctor_set(v___x_2089_, 1, v___f_2081_);
v___x_2090_ = l_StateRefT_x27_instMonad___redArg(v___x_2089_);
v___x_2091_ = lean_box(0);
v___x_2092_ = l_instInhabitedOfMonad___redArg(v___x_2090_, v___x_2091_);
v___f_2093_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2093_, 0, v___x_2092_);
v___x_2094_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_2066_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; uint8_t v___x_2096_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v___x_2096_ = lean_unbox(v_a_2095_);
switch(v___x_2096_)
{
case 0:
{
uint8_t v___x_2097_; lean_object* v___x_438__overap_2098_; lean_object* v___x_2099_; 
lean_dec_ref(v___f_2079_);
lean_dec_ref(v___f_2078_);
v___x_2097_ = lean_unbox(v_a_2095_);
lean_dec(v_a_2095_);
v___x_438__overap_2098_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___f_2093_, v___x_2097_, v_pu_2064_, v___f_2077_);
lean_dec_ref(v___f_2093_);
lean_inc(v_a_2069_);
lean_inc_ref(v_a_2068_);
lean_inc(v_a_2067_);
lean_inc_ref(v_a_2066_);
v___x_2099_ = lean_apply_5(v___x_438__overap_2098_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, lean_box(0));
return v___x_2099_;
}
case 1:
{
uint8_t v___x_2100_; lean_object* v___x_440__overap_2101_; lean_object* v___x_2102_; 
lean_dec_ref(v___f_2079_);
lean_dec_ref(v___f_2077_);
v___x_2100_ = lean_unbox(v_a_2095_);
lean_dec(v_a_2095_);
v___x_440__overap_2101_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___f_2093_, v___x_2100_, v_pu_2064_, v___f_2078_);
lean_dec_ref(v___f_2093_);
lean_inc(v_a_2069_);
lean_inc_ref(v_a_2068_);
lean_inc(v_a_2067_);
lean_inc_ref(v_a_2066_);
v___x_2102_ = lean_apply_5(v___x_440__overap_2101_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, lean_box(0));
return v___x_2102_;
}
default: 
{
uint8_t v___x_2103_; lean_object* v___x_442__overap_2104_; lean_object* v___x_2105_; 
lean_dec_ref(v___f_2078_);
lean_dec_ref(v___f_2077_);
v___x_2103_ = lean_unbox(v_a_2095_);
lean_dec(v_a_2095_);
v___x_442__overap_2104_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___f_2093_, v___x_2103_, v_pu_2064_, v___f_2079_);
lean_dec_ref(v___f_2093_);
lean_inc(v_a_2069_);
lean_inc_ref(v_a_2068_);
lean_inc(v_a_2067_);
lean_inc_ref(v_a_2066_);
v___x_2105_ = lean_apply_5(v___x_442__overap_2104_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, lean_box(0));
return v___x_2105_;
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec_ref(v___f_2093_);
lean_dec_ref(v___f_2079_);
lean_dec_ref(v___f_2078_);
lean_dec_ref(v___f_2077_);
v_a_2106_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2094_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2094_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___boxed(lean_object* v_pu_2114_, lean_object* v_decl_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
uint8_t v_pu_boxed_2121_; lean_object* v_res_2122_; 
v_pu_boxed_2121_ = lean_unbox(v_pu_2114_);
v_res_2122_ = l_Lean_Compiler_LCNF_Decl_save(v_pu_boxed_2121_, v_decl_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
return v_res_2122_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__3, &l_Lean_Compiler_LCNF_mkDeclExt___closed__3_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__3);
v___x_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
return v___x_2124_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2125_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0);
v___x_2126_ = lean_unsigned_to_nat(0u);
v___x_2127_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
lean_ctor_set(v___x_2127_, 2, v___x_2126_);
lean_ctor_set(v___x_2127_, 3, v___x_2126_);
lean_ctor_set(v___x_2127_, 4, v___x_2125_);
lean_ctor_set(v___x_2127_, 5, v___x_2125_);
lean_ctor_set(v___x_2127_, 6, v___x_2125_);
lean_ctor_set(v___x_2127_, 7, v___x_2125_);
lean_ctor_set(v___x_2127_, 8, v___x_2125_);
lean_ctor_set(v___x_2127_, 9, v___x_2125_);
lean_ctor_set(v___x_2127_, 10, v___x_2125_);
return v___x_2127_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2128_ = lean_unsigned_to_nat(32u);
v___x_2129_ = lean_mk_empty_array_with_capacity(v___x_2128_);
v___x_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
return v___x_2130_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2131_ = ((size_t)5ULL);
v___x_2132_ = lean_unsigned_to_nat(0u);
v___x_2133_ = lean_unsigned_to_nat(32u);
v___x_2134_ = lean_mk_empty_array_with_capacity(v___x_2133_);
v___x_2135_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2);
v___x_2136_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
lean_ctor_set(v___x_2136_, 1, v___x_2134_);
lean_ctor_set(v___x_2136_, 2, v___x_2132_);
lean_ctor_set(v___x_2136_, 3, v___x_2132_);
lean_ctor_set_usize(v___x_2136_, 4, v___x_2131_);
return v___x_2136_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2137_ = lean_box(1);
v___x_2138_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3);
v___x_2139_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0);
v___x_2140_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
lean_ctor_set(v___x_2140_, 1, v___x_2138_);
lean_ctor_set(v___x_2140_, 2, v___x_2137_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0(lean_object* v_msgData_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
lean_object* v___x_2145_; lean_object* v_toCold_2146_; lean_object* v_env_2147_; lean_object* v_options_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2145_ = lean_st_ref_get(v___y_2143_);
v_toCold_2146_ = lean_ctor_get(v___y_2142_, 0);
v_env_2147_ = lean_ctor_get(v___x_2145_, 0);
lean_inc_ref(v_env_2147_);
lean_dec(v___x_2145_);
v_options_2148_ = lean_ctor_get(v_toCold_2146_, 2);
v___x_2149_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1);
v___x_2150_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4);
lean_inc_ref(v_options_2148_);
v___x_2151_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2151_, 0, v_env_2147_);
lean_ctor_set(v___x_2151_, 1, v___x_2149_);
lean_ctor_set(v___x_2151_, 2, v___x_2150_);
lean_ctor_set(v___x_2151_, 3, v_options_2148_);
v___x_2152_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
lean_ctor_set(v___x_2152_, 1, v_msgData_2141_);
v___x_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___boxed(lean_object* v_msgData_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0(v_msgData_2154_, v___y_2155_, v___y_2156_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg(lean_object* v_msg_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v_ref_2163_; lean_object* v___x_2164_; lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2173_; 
v_ref_2163_ = lean_ctor_get(v___y_2160_, 2);
v___x_2164_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0(v_msg_2159_, v___y_2160_, v___y_2161_);
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2167_ = v___x_2164_;
v_isShared_2168_ = v_isSharedCheck_2173_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2164_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2173_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2169_; lean_object* v___x_2171_; 
lean_inc(v_ref_2163_);
v___x_2169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2169_, 0, v_ref_2163_);
lean_ctor_set(v___x_2169_, 1, v_a_2165_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set_tag(v___x_2167_, 1);
lean_ctor_set(v___x_2167_, 0, v___x_2169_);
v___x_2171_ = v___x_2167_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg___boxed(lean_object* v_msg_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg(v_msg_2174_, v___y_2175_, v___y_2176_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
return v_res_2178_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = ((lean_object*)(l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__0));
v___x_2181_ = l_Lean_stringToMessageData(v___x_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f(lean_object* v_declName_2182_, uint8_t v_phase_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_){
_start:
{
switch(v_phase_2183_)
{
case 0:
{
lean_object* v___x_2187_; 
v___x_2187_ = l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg(v_declName_2182_, v_a_2185_);
return v___x_2187_;
}
case 1:
{
lean_object* v___x_2188_; 
v___x_2188_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_2182_, v_a_2185_);
return v___x_2188_;
}
default: 
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
lean_dec(v_declName_2182_);
v___x_2189_ = lean_obj_once(&l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1, &l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1_once, _init_l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1);
v___x_2190_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg(v___x_2189_, v_a_2184_, v_a_2185_);
return v___x_2190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f___boxed(lean_object* v_declName_2191_, lean_object* v_phase_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_){
_start:
{
uint8_t v_phase_boxed_2196_; lean_object* v_res_2197_; 
v_phase_boxed_2196_ = lean_unbox(v_phase_2192_);
v_res_2197_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_2191_, v_phase_boxed_2196_, v_a_2193_, v_a_2194_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0(lean_object* v_00_u03b1_2198_, lean_object* v_msg_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v___x_2203_; 
v___x_2203_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg(v_msg_2199_, v___y_2200_, v___y_2201_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___boxed(lean_object* v_00_u03b1_2204_, lean_object* v_msg_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0(v_00_u03b1_2204_, v_msg_2205_, v___y_2206_, v___y_2207_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg(lean_object* v_declName_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_2211_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; uint8_t v___x_2217_; lean_object* v___x_2218_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref_known(v___x_2215_, 1);
v___x_2217_ = lean_unbox(v_a_2216_);
v___x_2218_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_2210_, v___x_2217_, v_a_2212_, v_a_2213_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2242_; 
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2221_ = v___x_2218_;
v_isShared_2222_ = v_isSharedCheck_2242_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2218_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2242_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
if (lean_obj_tag(v_a_2219_) == 1)
{
lean_object* v_val_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2237_; 
v_val_2223_ = lean_ctor_get(v_a_2219_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_a_2219_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2225_ = v_a_2219_;
v_isShared_2226_ = v_isSharedCheck_2237_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_val_2223_);
lean_dec(v_a_2219_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2237_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
uint8_t v___x_2227_; uint8_t v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2232_; 
v___x_2227_ = lean_unbox(v_a_2216_);
lean_dec(v_a_2216_);
v___x_2228_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_2227_);
v___x_2229_ = lean_box(v___x_2228_);
v___x_2230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
lean_ctor_set(v___x_2230_, 1, v_val_2223_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v___x_2230_);
v___x_2232_ = v___x_2225_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2230_);
v___x_2232_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
lean_object* v___x_2234_; 
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 0, v___x_2232_);
v___x_2234_ = v___x_2221_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2240_; 
lean_dec(v_a_2219_);
lean_dec(v_a_2216_);
v___x_2238_ = lean_box(0);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 0, v___x_2238_);
v___x_2240_ = v___x_2221_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2238_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
lean_dec(v_a_2216_);
v_a_2243_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2218_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2218_);
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
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
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
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_dec(v_declName_2210_);
v_a_2251_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2215_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2215_);
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
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg___boxed(lean_object* v_declName_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(v_declName_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
lean_dec(v_a_2262_);
lean_dec_ref(v_a_2261_);
lean_dec_ref(v_a_2260_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDecl_x3f(lean_object* v_declName_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_2266_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; uint8_t v___x_2273_; lean_object* v___x_2274_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2272_);
lean_dec_ref_known(v___x_2271_, 1);
v___x_2273_ = lean_unbox(v_a_2272_);
v___x_2274_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_2265_, v___x_2273_, v_a_2268_, v_a_2269_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2298_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2277_ = v___x_2274_;
v_isShared_2278_ = v_isSharedCheck_2298_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2274_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2298_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
if (lean_obj_tag(v_a_2275_) == 1)
{
lean_object* v_val_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2293_; 
v_val_2279_ = lean_ctor_get(v_a_2275_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v_a_2275_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2281_ = v_a_2275_;
v_isShared_2282_ = v_isSharedCheck_2293_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_val_2279_);
lean_dec(v_a_2275_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2293_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
uint8_t v___x_2283_; uint8_t v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2288_; 
v___x_2283_ = lean_unbox(v_a_2272_);
lean_dec(v_a_2272_);
v___x_2284_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_2283_);
v___x_2285_ = lean_box(v___x_2284_);
v___x_2286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
lean_ctor_set(v___x_2286_, 1, v_val_2279_);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v___x_2286_);
v___x_2288_ = v___x_2281_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2290_; 
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v___x_2288_);
v___x_2290_ = v___x_2277_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
else
{
lean_object* v___x_2294_; lean_object* v___x_2296_; 
lean_dec(v_a_2275_);
lean_dec(v_a_2272_);
v___x_2294_ = lean_box(0);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v___x_2294_);
v___x_2296_ = v___x_2277_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2294_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec(v_a_2272_);
v_a_2299_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2274_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2274_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec(v_declName_2265_);
v_a_2307_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2271_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2271_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___boxed(lean_object* v_declName_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_Lean_Compiler_LCNF_getDecl_x3f(v_declName_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
lean_dec(v_a_2319_);
lean_dec_ref(v_a_2318_);
lean_dec(v_a_2317_);
lean_dec_ref(v_a_2316_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(lean_object* v_declName_2322_, uint8_t v_phase_2323_, lean_object* v_a_2324_){
_start:
{
lean_object* v___x_2326_; 
v___x_2326_ = lean_obj_once(&l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg___closed__0, &l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_getDeclCore_x3f___redArg___closed__0);
switch(v_phase_2323_)
{
case 0:
{
lean_object* v___x_2327_; lean_object* v_env_2328_; lean_object* v___x_2329_; lean_object* v_toEnvExtension_2330_; lean_object* v_asyncMode_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2327_ = lean_st_ref_get(v_a_2324_);
v_env_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc_ref(v_env_2328_);
lean_dec(v___x_2327_);
v___x_2329_ = l_Lean_Compiler_LCNF_baseExt;
v_toEnvExtension_2330_ = lean_ctor_get(v___x_2329_, 0);
v_asyncMode_2331_ = lean_ctor_get(v_toEnvExtension_2330_, 2);
v___x_2332_ = lean_box(0);
v___x_2333_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2326_, v___x_2329_, v_env_2328_, v_asyncMode_2331_, v___x_2332_);
v___x_2334_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_2333_, v_declName_2322_);
lean_dec(v___x_2333_);
v___x_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
return v___x_2335_;
}
case 1:
{
lean_object* v___x_2336_; lean_object* v_env_2337_; lean_object* v___x_2338_; lean_object* v_toEnvExtension_2339_; lean_object* v_asyncMode_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2336_ = lean_st_ref_get(v_a_2324_);
v_env_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc_ref(v_env_2337_);
lean_dec(v___x_2336_);
v___x_2338_ = l_Lean_Compiler_LCNF_monoExt;
v_toEnvExtension_2339_ = lean_ctor_get(v___x_2338_, 0);
v_asyncMode_2340_ = lean_ctor_get(v_toEnvExtension_2339_, 2);
v___x_2341_ = lean_box(0);
v___x_2342_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2326_, v___x_2338_, v_env_2337_, v_asyncMode_2340_, v___x_2341_);
v___x_2343_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_2342_, v_declName_2322_);
lean_dec(v___x_2342_);
v___x_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2343_);
return v___x_2344_;
}
default: 
{
lean_object* v___x_2345_; lean_object* v_env_2346_; lean_object* v___x_2347_; lean_object* v_asyncMode_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2345_ = lean_st_ref_get(v_a_2324_);
v_env_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc_ref(v_env_2346_);
lean_dec(v___x_2345_);
v___x_2347_ = l_Lean_Compiler_LCNF_impureExt;
v_asyncMode_2348_ = lean_ctor_get(v___x_2347_, 2);
v___x_2349_ = lean_box(0);
v___x_2350_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2326_, v___x_2347_, v_env_2346_, v_asyncMode_2348_, v___x_2349_);
v___x_2351_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_2350_, v_declName_2322_);
lean_dec(v___x_2350_);
v___x_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
return v___x_2352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg___boxed(lean_object* v_declName_2353_, lean_object* v_phase_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_){
_start:
{
uint8_t v_phase_boxed_2357_; lean_object* v_res_2358_; 
v_phase_boxed_2357_ = lean_unbox(v_phase_2354_);
v_res_2358_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_declName_2353_, v_phase_boxed_2357_, v_a_2355_);
lean_dec(v_a_2355_);
lean_dec(v_declName_2353_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f(lean_object* v_declName_2359_, uint8_t v_phase_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_declName_2359_, v_phase_2360_, v_a_2364_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___boxed(lean_object* v_declName_2367_, lean_object* v_phase_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_){
_start:
{
uint8_t v_phase_boxed_2374_; lean_object* v_res_2375_; 
v_phase_boxed_2374_ = lean_unbox(v_phase_2368_);
v_res_2375_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f(v_declName_2367_, v_phase_boxed_2374_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
lean_dec(v_a_2372_);
lean_dec_ref(v_a_2371_);
lean_dec(v_a_2370_);
lean_dec_ref(v_a_2369_);
lean_dec(v_declName_2367_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDecl_x3f___redArg(lean_object* v_declName_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_2377_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; uint8_t v___x_2382_; lean_object* v___x_2383_; lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2407_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2381_);
lean_dec_ref_known(v___x_2380_, 1);
v___x_2382_ = lean_unbox(v_a_2381_);
v___x_2383_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_declName_2376_, v___x_2382_, v_a_2378_);
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2386_ = v___x_2383_;
v_isShared_2387_ = v_isSharedCheck_2407_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2383_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2407_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
if (lean_obj_tag(v_a_2384_) == 1)
{
lean_object* v_val_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2402_; 
v_val_2388_ = lean_ctor_get(v_a_2384_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v_a_2384_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2390_ = v_a_2384_;
v_isShared_2391_ = v_isSharedCheck_2402_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_val_2388_);
lean_dec(v_a_2384_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2402_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
uint8_t v___x_2392_; uint8_t v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2397_; 
v___x_2392_ = lean_unbox(v_a_2381_);
lean_dec(v_a_2381_);
v___x_2393_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_2392_);
v___x_2394_ = lean_box(v___x_2393_);
v___x_2395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2394_);
lean_ctor_set(v___x_2395_, 1, v_val_2388_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v___x_2395_);
v___x_2397_ = v___x_2390_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
lean_object* v___x_2399_; 
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 0, v___x_2397_);
v___x_2399_ = v___x_2386_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v___x_2397_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
else
{
lean_object* v___x_2403_; lean_object* v___x_2405_; 
lean_dec(v_a_2384_);
lean_dec(v_a_2381_);
v___x_2403_ = lean_box(0);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 0, v___x_2403_);
v___x_2405_ = v___x_2386_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
else
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2415_; 
v_a_2408_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2410_ = v___x_2380_;
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2380_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
if (v_isShared_2411_ == 0)
{
v___x_2413_ = v___x_2410_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDecl_x3f___redArg___boxed(lean_object* v_declName_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Lean_Compiler_LCNF_getLocalDecl_x3f___redArg(v_declName_2416_, v_a_2417_, v_a_2418_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
lean_dec(v_declName_2416_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDecl_x3f(lean_object* v_declName_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v___x_2427_; 
v___x_2427_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_2422_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v_a_2428_; uint8_t v___x_2429_; lean_object* v___x_2430_; lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2454_; 
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_a_2428_);
lean_dec_ref_known(v___x_2427_, 1);
v___x_2429_ = lean_unbox(v_a_2428_);
v___x_2430_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_declName_2421_, v___x_2429_, v_a_2425_);
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2433_ = v___x_2430_;
v_isShared_2434_ = v_isSharedCheck_2454_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2430_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2454_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
if (lean_obj_tag(v_a_2431_) == 1)
{
lean_object* v_val_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2449_; 
v_val_2435_ = lean_ctor_get(v_a_2431_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v_a_2431_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2437_ = v_a_2431_;
v_isShared_2438_ = v_isSharedCheck_2449_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_val_2435_);
lean_dec(v_a_2431_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2449_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
uint8_t v___x_2439_; uint8_t v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2444_; 
v___x_2439_ = lean_unbox(v_a_2428_);
lean_dec(v_a_2428_);
v___x_2440_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_2439_);
v___x_2441_ = lean_box(v___x_2440_);
v___x_2442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
lean_ctor_set(v___x_2442_, 1, v_val_2435_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 0, v___x_2442_);
v___x_2444_ = v___x_2437_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v___x_2442_);
v___x_2444_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
lean_object* v___x_2446_; 
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 0, v___x_2444_);
v___x_2446_ = v___x_2433_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v___x_2444_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
else
{
lean_object* v___x_2450_; lean_object* v___x_2452_; 
lean_dec(v_a_2431_);
lean_dec(v_a_2428_);
v___x_2450_ = lean_box(0);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 0, v___x_2450_);
v___x_2452_ = v___x_2433_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v___x_2450_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
else
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
v_a_2455_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2427_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2427_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDecl_x3f___boxed(lean_object* v_declName_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l_Lean_Compiler_LCNF_getLocalDecl_x3f(v_declName_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_);
lean_dec(v_a_2467_);
lean_dec_ref(v_a_2466_);
lean_dec(v_a_2465_);
lean_dec_ref(v_a_2464_);
lean_dec(v_declName_2463_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2____boxed(lean_object* v_a_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2_();
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_recordFinalImpureDecl___lam__0(lean_object* v_name_2474_, lean_object* v_s_2475_){
_start:
{
lean_object* v_fst_2476_; lean_object* v_snd_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2486_; 
v_fst_2476_ = lean_ctor_get(v_s_2475_, 0);
v_snd_2477_ = lean_ctor_get(v_s_2475_, 1);
v_isSharedCheck_2486_ = !lean_is_exclusive(v_s_2475_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2479_ = v_s_2475_;
v_isShared_2480_ = v_isSharedCheck_2486_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_snd_2477_);
lean_inc(v_fst_2476_);
lean_dec(v_s_2475_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2486_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2484_; 
lean_inc(v_name_2474_);
v___x_2481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2481_, 0, v_name_2474_);
lean_ctor_set(v___x_2481_, 1, v_fst_2476_);
v___x_2482_ = l_Lean_NameSet_insert(v_snd_2477_, v_name_2474_);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 1, v___x_2482_);
lean_ctor_set(v___x_2479_, 0, v___x_2481_);
v___x_2484_ = v___x_2479_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2481_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v___x_2482_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_recordFinalImpureDecl(lean_object* v_env_2487_, lean_object* v_name_2488_){
_start:
{
lean_object* v___x_2489_; lean_object* v_asyncMode_2490_; lean_object* v___f_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2489_ = l_Lean_Compiler_LCNF_declOrderExt;
v_asyncMode_2490_ = lean_ctor_get(v___x_2489_, 2);
v___f_2491_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_recordFinalImpureDecl___lam__0), 2, 1);
lean_closure_set(v___f_2491_, 0, v_name_2488_);
v___x_2492_ = lean_box(0);
v___x_2493_ = l_Lean_EnvExtension_modifyState___redArg(v___x_2489_, v_env_2487_, v___f_2491_, v_asyncMode_2490_, v___x_2492_);
return v___x_2493_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7(void){
_start:
{
lean_object* v___x_2501_; 
v___x_2501_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1(lean_object* v_msg_2502_){
_start:
{
lean_object* v___f_2503_; lean_object* v___f_2504_; lean_object* v___f_2505_; lean_object* v___f_2506_; lean_object* v___f_2507_; lean_object* v___f_2508_; lean_object* v___f_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___f_2503_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__0));
v___f_2504_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__1));
v___f_2505_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__2));
v___f_2506_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__3));
v___f_2507_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__4));
v___f_2508_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__5));
v___f_2509_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__6));
v___x_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___f_2503_);
lean_ctor_set(v___x_2510_, 1, v___f_2504_);
v___x_2511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
lean_ctor_set(v___x_2511_, 1, v___f_2505_);
lean_ctor_set(v___x_2511_, 2, v___f_2506_);
lean_ctor_set(v___x_2511_, 3, v___f_2507_);
lean_ctor_set(v___x_2511_, 4, v___f_2508_);
v___x_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2511_);
lean_ctor_set(v___x_2512_, 1, v___f_2509_);
v___x_2513_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7, &l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7_once, _init_l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7);
v___x_2514_ = lean_unsigned_to_nat(0u);
v___x_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2513_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
v___x_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2515_);
v___x_2517_ = l_instInhabitedOfMonad___redArg(v___x_2512_, v___x_2516_);
v___x_2518_ = lean_panic_fn_borrowed(v___x_2517_, v_msg_2502_);
lean_dec(v___x_2517_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__5(lean_object* v_msg_2519_){
_start:
{
lean_object* v___f_2520_; lean_object* v___f_2521_; lean_object* v___f_2522_; lean_object* v___f_2523_; lean_object* v___f_2524_; lean_object* v___f_2525_; lean_object* v___f_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___f_2520_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__0));
v___f_2521_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__1));
v___f_2522_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__2));
v___f_2523_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__3));
v___f_2524_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__4));
v___f_2525_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__5));
v___f_2526_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__6));
v___x_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___f_2520_);
lean_ctor_set(v___x_2527_, 1, v___f_2521_);
v___x_2528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
lean_ctor_set(v___x_2528_, 1, v___f_2522_);
lean_ctor_set(v___x_2528_, 2, v___f_2523_);
lean_ctor_set(v___x_2528_, 3, v___f_2524_);
lean_ctor_set(v___x_2528_, 4, v___f_2525_);
v___x_2529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
lean_ctor_set(v___x_2529_, 1, v___f_2526_);
v___x_2530_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7, &l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7_once, _init_l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7);
v___x_2531_ = l_instInhabitedOfMonad___redArg(v___x_2529_, v___x_2530_);
v___x_2532_ = lean_panic_fn_borrowed(v___x_2531_, v_msg_2519_);
lean_dec(v___x_2531_);
return v___x_2532_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(lean_object* v_a_2533_, lean_object* v_x_2534_){
_start:
{
if (lean_obj_tag(v_x_2534_) == 0)
{
uint8_t v___x_2535_; 
v___x_2535_ = 0;
return v___x_2535_;
}
else
{
lean_object* v_key_2536_; lean_object* v_tail_2537_; uint8_t v___x_2538_; 
v_key_2536_ = lean_ctor_get(v_x_2534_, 0);
v_tail_2537_ = lean_ctor_get(v_x_2534_, 2);
v___x_2538_ = lean_name_eq(v_key_2536_, v_a_2533_);
if (v___x_2538_ == 0)
{
v_x_2534_ = v_tail_2537_;
goto _start;
}
else
{
return v___x_2538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg___boxed(lean_object* v_a_2540_, lean_object* v_x_2541_){
_start:
{
uint8_t v_res_2542_; lean_object* v_r_2543_; 
v_res_2542_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_2540_, v_x_2541_);
lean_dec(v_x_2541_);
lean_dec(v_a_2540_);
v_r_2543_ = lean_box(v_res_2542_);
return v_r_2543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8_spec__10___redArg(lean_object* v_x_2544_, lean_object* v_x_2545_){
_start:
{
if (lean_obj_tag(v_x_2545_) == 0)
{
return v_x_2544_;
}
else
{
lean_object* v_key_2546_; lean_object* v_value_2547_; lean_object* v_tail_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2574_; 
v_key_2546_ = lean_ctor_get(v_x_2545_, 0);
v_value_2547_ = lean_ctor_get(v_x_2545_, 1);
v_tail_2548_ = lean_ctor_get(v_x_2545_, 2);
v_isSharedCheck_2574_ = !lean_is_exclusive(v_x_2545_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2550_ = v_x_2545_;
v_isShared_2551_ = v_isSharedCheck_2574_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_tail_2548_);
lean_inc(v_value_2547_);
lean_inc(v_key_2546_);
lean_dec(v_x_2545_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2574_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2552_; uint64_t v___y_2554_; 
v___x_2552_ = lean_array_get_size(v_x_2544_);
if (lean_obj_tag(v_key_2546_) == 0)
{
uint64_t v___x_2572_; 
v___x_2572_ = 1723ULL;
v___y_2554_ = v___x_2572_;
goto v___jp_2553_;
}
else
{
uint64_t v_hash_2573_; 
v_hash_2573_ = lean_ctor_get_uint64(v_key_2546_, sizeof(void*)*2);
v___y_2554_ = v_hash_2573_;
goto v___jp_2553_;
}
v___jp_2553_:
{
uint64_t v___x_2555_; uint64_t v___x_2556_; uint64_t v_fold_2557_; uint64_t v___x_2558_; uint64_t v___x_2559_; uint64_t v___x_2560_; size_t v___x_2561_; size_t v___x_2562_; size_t v___x_2563_; size_t v___x_2564_; size_t v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2568_; 
v___x_2555_ = 32ULL;
v___x_2556_ = lean_uint64_shift_right(v___y_2554_, v___x_2555_);
v_fold_2557_ = lean_uint64_xor(v___y_2554_, v___x_2556_);
v___x_2558_ = 16ULL;
v___x_2559_ = lean_uint64_shift_right(v_fold_2557_, v___x_2558_);
v___x_2560_ = lean_uint64_xor(v_fold_2557_, v___x_2559_);
v___x_2561_ = lean_uint64_to_usize(v___x_2560_);
v___x_2562_ = lean_usize_of_nat(v___x_2552_);
v___x_2563_ = ((size_t)1ULL);
v___x_2564_ = lean_usize_sub(v___x_2562_, v___x_2563_);
v___x_2565_ = lean_usize_land(v___x_2561_, v___x_2564_);
v___x_2566_ = lean_array_uget_borrowed(v_x_2544_, v___x_2565_);
lean_inc(v___x_2566_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 2, v___x_2566_);
v___x_2568_ = v___x_2550_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_key_2546_);
lean_ctor_set(v_reuseFailAlloc_2571_, 1, v_value_2547_);
lean_ctor_set(v_reuseFailAlloc_2571_, 2, v___x_2566_);
v___x_2568_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
lean_object* v___x_2569_; 
v___x_2569_ = lean_array_uset(v_x_2544_, v___x_2565_, v___x_2568_);
v_x_2544_ = v___x_2569_;
v_x_2545_ = v_tail_2548_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8___redArg(lean_object* v_i_2575_, lean_object* v_source_2576_, lean_object* v_target_2577_){
_start:
{
lean_object* v___x_2578_; uint8_t v___x_2579_; 
v___x_2578_ = lean_array_get_size(v_source_2576_);
v___x_2579_ = lean_nat_dec_lt(v_i_2575_, v___x_2578_);
if (v___x_2579_ == 0)
{
lean_dec_ref(v_source_2576_);
lean_dec(v_i_2575_);
return v_target_2577_;
}
else
{
lean_object* v_es_2580_; lean_object* v___x_2581_; lean_object* v_source_2582_; lean_object* v_target_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v_es_2580_ = lean_array_fget(v_source_2576_, v_i_2575_);
v___x_2581_ = lean_box(0);
v_source_2582_ = lean_array_fset(v_source_2576_, v_i_2575_, v___x_2581_);
v_target_2583_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8_spec__10___redArg(v_target_2577_, v_es_2580_);
v___x_2584_ = lean_unsigned_to_nat(1u);
v___x_2585_ = lean_nat_add(v_i_2575_, v___x_2584_);
lean_dec(v_i_2575_);
v_i_2575_ = v___x_2585_;
v_source_2576_ = v_source_2582_;
v_target_2577_ = v_target_2583_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6___redArg(lean_object* v_data_2587_){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v_nbuckets_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2588_ = lean_array_get_size(v_data_2587_);
v___x_2589_ = lean_unsigned_to_nat(2u);
v_nbuckets_2590_ = lean_nat_mul(v___x_2588_, v___x_2589_);
v___x_2591_ = lean_unsigned_to_nat(0u);
v___x_2592_ = lean_box(0);
v___x_2593_ = lean_mk_array(v_nbuckets_2590_, v___x_2592_);
v___x_2594_ = lean_array_propagate_mark(v_data_2587_, v___x_2593_);
v___x_2595_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8___redArg(v___x_2591_, v_data_2587_, v___x_2594_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__0___redArg(lean_object* v_m_2596_, lean_object* v_a_2597_, lean_object* v_b_2598_){
_start:
{
lean_object* v_size_2599_; lean_object* v_buckets_2600_; lean_object* v___x_2601_; uint64_t v___y_2603_; 
v_size_2599_ = lean_ctor_get(v_m_2596_, 0);
v_buckets_2600_ = lean_ctor_get(v_m_2596_, 1);
v___x_2601_ = lean_array_get_size(v_buckets_2600_);
if (lean_obj_tag(v_a_2597_) == 0)
{
uint64_t v___x_2640_; 
v___x_2640_ = 1723ULL;
v___y_2603_ = v___x_2640_;
goto v___jp_2602_;
}
else
{
uint64_t v_hash_2641_; 
v_hash_2641_ = lean_ctor_get_uint64(v_a_2597_, sizeof(void*)*2);
v___y_2603_ = v_hash_2641_;
goto v___jp_2602_;
}
v___jp_2602_:
{
uint64_t v___x_2604_; uint64_t v___x_2605_; uint64_t v_fold_2606_; uint64_t v___x_2607_; uint64_t v___x_2608_; uint64_t v___x_2609_; size_t v___x_2610_; size_t v___x_2611_; size_t v___x_2612_; size_t v___x_2613_; size_t v___x_2614_; lean_object* v_bkt_2615_; uint8_t v___x_2616_; 
v___x_2604_ = 32ULL;
v___x_2605_ = lean_uint64_shift_right(v___y_2603_, v___x_2604_);
v_fold_2606_ = lean_uint64_xor(v___y_2603_, v___x_2605_);
v___x_2607_ = 16ULL;
v___x_2608_ = lean_uint64_shift_right(v_fold_2606_, v___x_2607_);
v___x_2609_ = lean_uint64_xor(v_fold_2606_, v___x_2608_);
v___x_2610_ = lean_uint64_to_usize(v___x_2609_);
v___x_2611_ = lean_usize_of_nat(v___x_2601_);
v___x_2612_ = ((size_t)1ULL);
v___x_2613_ = lean_usize_sub(v___x_2611_, v___x_2612_);
v___x_2614_ = lean_usize_land(v___x_2610_, v___x_2613_);
v_bkt_2615_ = lean_array_uget_borrowed(v_buckets_2600_, v___x_2614_);
v___x_2616_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_2597_, v_bkt_2615_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2637_; 
lean_inc_ref(v_buckets_2600_);
lean_inc(v_size_2599_);
v_isSharedCheck_2637_ = !lean_is_exclusive(v_m_2596_);
if (v_isSharedCheck_2637_ == 0)
{
lean_object* v_unused_2638_; lean_object* v_unused_2639_; 
v_unused_2638_ = lean_ctor_get(v_m_2596_, 1);
lean_dec(v_unused_2638_);
v_unused_2639_ = lean_ctor_get(v_m_2596_, 0);
lean_dec(v_unused_2639_);
v___x_2618_ = v_m_2596_;
v_isShared_2619_ = v_isSharedCheck_2637_;
goto v_resetjp_2617_;
}
else
{
lean_dec(v_m_2596_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2637_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2620_; lean_object* v_size_x27_2621_; lean_object* v___x_2622_; lean_object* v_buckets_x27_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; uint8_t v___x_2629_; 
v___x_2620_ = lean_unsigned_to_nat(1u);
v_size_x27_2621_ = lean_nat_add(v_size_2599_, v___x_2620_);
lean_dec(v_size_2599_);
lean_inc(v_bkt_2615_);
v___x_2622_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2622_, 0, v_a_2597_);
lean_ctor_set(v___x_2622_, 1, v_b_2598_);
lean_ctor_set(v___x_2622_, 2, v_bkt_2615_);
v_buckets_x27_2623_ = lean_array_uset(v_buckets_2600_, v___x_2614_, v___x_2622_);
v___x_2624_ = lean_unsigned_to_nat(4u);
v___x_2625_ = lean_nat_mul(v_size_x27_2621_, v___x_2624_);
v___x_2626_ = lean_unsigned_to_nat(3u);
v___x_2627_ = lean_nat_div(v___x_2625_, v___x_2626_);
lean_dec(v___x_2625_);
v___x_2628_ = lean_array_get_size(v_buckets_x27_2623_);
v___x_2629_ = lean_nat_dec_le(v___x_2627_, v___x_2628_);
lean_dec(v___x_2627_);
if (v___x_2629_ == 0)
{
lean_object* v_val_2630_; lean_object* v___x_2632_; 
v_val_2630_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6___redArg(v_buckets_x27_2623_);
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 1, v_val_2630_);
lean_ctor_set(v___x_2618_, 0, v_size_x27_2621_);
v___x_2632_ = v___x_2618_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_size_x27_2621_);
lean_ctor_set(v_reuseFailAlloc_2633_, 1, v_val_2630_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
else
{
lean_object* v___x_2635_; 
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 1, v_buckets_x27_2623_);
lean_ctor_set(v___x_2618_, 0, v_size_x27_2621_);
v___x_2635_ = v___x_2618_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_size_x27_2621_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_buckets_x27_2623_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
else
{
lean_dec(v_b_2598_);
lean_dec(v_a_2597_);
return v_m_2596_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__1(lean_object* v_as_2642_, size_t v_sz_2643_, size_t v_i_2644_, lean_object* v_b_2645_){
_start:
{
uint8_t v___x_2646_; 
v___x_2646_ = lean_usize_dec_lt(v_i_2644_, v_sz_2643_);
if (v___x_2646_ == 0)
{
return v_b_2645_;
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2648_; lean_object* v_r_2649_; size_t v___x_2650_; size_t v___x_2651_; 
v_a_2647_ = lean_array_uget_borrowed(v_as_2642_, v_i_2644_);
v___x_2648_ = lean_box(0);
lean_inc(v_a_2647_);
v_r_2649_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__0___redArg(v_b_2645_, v_a_2647_, v___x_2648_);
v___x_2650_ = ((size_t)1ULL);
v___x_2651_ = lean_usize_add(v_i_2644_, v___x_2650_);
v_i_2644_ = v___x_2651_;
v_b_2645_ = v_r_2649_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__1___boxed(lean_object* v_as_2653_, lean_object* v_sz_2654_, lean_object* v_i_2655_, lean_object* v_b_2656_){
_start:
{
size_t v_sz_boxed_2657_; size_t v_i_boxed_2658_; lean_object* v_res_2659_; 
v_sz_boxed_2657_ = lean_unbox_usize(v_sz_2654_);
lean_dec(v_sz_2654_);
v_i_boxed_2658_ = lean_unbox_usize(v_i_2655_);
lean_dec(v_i_2655_);
v_res_2659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__1(v_as_2653_, v_sz_boxed_2657_, v_i_boxed_2658_, v_b_2656_);
lean_dec_ref(v_as_2653_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0(lean_object* v_m_2660_, lean_object* v_l_2661_){
_start:
{
size_t v_sz_2662_; size_t v___x_2663_; lean_object* v___x_2664_; 
v_sz_2662_ = lean_array_size(v_l_2661_);
v___x_2663_ = ((size_t)0ULL);
v___x_2664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__1(v_l_2661_, v_sz_2662_, v___x_2663_, v_m_2660_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0___boxed(lean_object* v_m_2665_, lean_object* v_l_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0(v_m_2665_, v_l_2666_);
lean_dec_ref(v_l_2666_);
return v_res_2667_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg(lean_object* v_m_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v_buckets_2670_; lean_object* v___x_2671_; uint64_t v___y_2673_; 
v_buckets_2670_ = lean_ctor_get(v_m_2668_, 1);
v___x_2671_ = lean_array_get_size(v_buckets_2670_);
if (lean_obj_tag(v_a_2669_) == 0)
{
uint64_t v___x_2687_; 
v___x_2687_ = 1723ULL;
v___y_2673_ = v___x_2687_;
goto v___jp_2672_;
}
else
{
uint64_t v_hash_2688_; 
v_hash_2688_ = lean_ctor_get_uint64(v_a_2669_, sizeof(void*)*2);
v___y_2673_ = v_hash_2688_;
goto v___jp_2672_;
}
v___jp_2672_:
{
uint64_t v___x_2674_; uint64_t v___x_2675_; uint64_t v_fold_2676_; uint64_t v___x_2677_; uint64_t v___x_2678_; uint64_t v___x_2679_; size_t v___x_2680_; size_t v___x_2681_; size_t v___x_2682_; size_t v___x_2683_; size_t v___x_2684_; lean_object* v___x_2685_; uint8_t v___x_2686_; 
v___x_2674_ = 32ULL;
v___x_2675_ = lean_uint64_shift_right(v___y_2673_, v___x_2674_);
v_fold_2676_ = lean_uint64_xor(v___y_2673_, v___x_2675_);
v___x_2677_ = 16ULL;
v___x_2678_ = lean_uint64_shift_right(v_fold_2676_, v___x_2677_);
v___x_2679_ = lean_uint64_xor(v_fold_2676_, v___x_2678_);
v___x_2680_ = lean_uint64_to_usize(v___x_2679_);
v___x_2681_ = lean_usize_of_nat(v___x_2671_);
v___x_2682_ = ((size_t)1ULL);
v___x_2683_ = lean_usize_sub(v___x_2681_, v___x_2682_);
v___x_2684_ = lean_usize_land(v___x_2680_, v___x_2683_);
v___x_2685_ = lean_array_uget_borrowed(v_buckets_2670_, v___x_2684_);
v___x_2686_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_2669_, v___x_2685_);
return v___x_2686_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg___boxed(lean_object* v_m_2689_, lean_object* v_a_2690_){
_start:
{
uint8_t v_res_2691_; lean_object* v_r_2692_; 
v_res_2691_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg(v_m_2689_, v_a_2690_);
lean_dec(v_a_2690_);
lean_dec_ref(v_m_2689_);
v_r_2692_ = lean_box(v_res_2691_);
return v_r_2692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7___redArg(lean_object* v_a_2693_, lean_object* v_b_2694_, lean_object* v_x_2695_){
_start:
{
if (lean_obj_tag(v_x_2695_) == 0)
{
lean_dec(v_b_2694_);
lean_dec(v_a_2693_);
return v_x_2695_;
}
else
{
lean_object* v_key_2696_; lean_object* v_value_2697_; lean_object* v_tail_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2710_; 
v_key_2696_ = lean_ctor_get(v_x_2695_, 0);
v_value_2697_ = lean_ctor_get(v_x_2695_, 1);
v_tail_2698_ = lean_ctor_get(v_x_2695_, 2);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_x_2695_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2700_ = v_x_2695_;
v_isShared_2701_ = v_isSharedCheck_2710_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_tail_2698_);
lean_inc(v_value_2697_);
lean_inc(v_key_2696_);
lean_dec(v_x_2695_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2710_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
uint8_t v___x_2702_; 
v___x_2702_ = lean_name_eq(v_key_2696_, v_a_2693_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2703_; lean_object* v___x_2705_; 
v___x_2703_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7___redArg(v_a_2693_, v_b_2694_, v_tail_2698_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 2, v___x_2703_);
v___x_2705_ = v___x_2700_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_key_2696_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v_value_2697_);
lean_ctor_set(v_reuseFailAlloc_2706_, 2, v___x_2703_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
else
{
lean_object* v___x_2708_; 
lean_dec(v_value_2697_);
lean_dec(v_key_2696_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 1, v_b_2694_);
lean_ctor_set(v___x_2700_, 0, v_a_2693_);
v___x_2708_ = v___x_2700_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2693_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_b_2694_);
lean_ctor_set(v_reuseFailAlloc_2709_, 2, v_tail_2698_);
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
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3___redArg(lean_object* v_m_2711_, lean_object* v_a_2712_, lean_object* v_b_2713_){
_start:
{
lean_object* v_size_2714_; lean_object* v_buckets_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2761_; 
v_size_2714_ = lean_ctor_get(v_m_2711_, 0);
v_buckets_2715_ = lean_ctor_get(v_m_2711_, 1);
v_isSharedCheck_2761_ = !lean_is_exclusive(v_m_2711_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2717_ = v_m_2711_;
v_isShared_2718_ = v_isSharedCheck_2761_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_buckets_2715_);
lean_inc(v_size_2714_);
lean_dec(v_m_2711_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2761_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2719_; uint64_t v___y_2721_; 
v___x_2719_ = lean_array_get_size(v_buckets_2715_);
if (lean_obj_tag(v_a_2712_) == 0)
{
uint64_t v___x_2759_; 
v___x_2759_ = 1723ULL;
v___y_2721_ = v___x_2759_;
goto v___jp_2720_;
}
else
{
uint64_t v_hash_2760_; 
v_hash_2760_ = lean_ctor_get_uint64(v_a_2712_, sizeof(void*)*2);
v___y_2721_ = v_hash_2760_;
goto v___jp_2720_;
}
v___jp_2720_:
{
uint64_t v___x_2722_; uint64_t v___x_2723_; uint64_t v_fold_2724_; uint64_t v___x_2725_; uint64_t v___x_2726_; uint64_t v___x_2727_; size_t v___x_2728_; size_t v___x_2729_; size_t v___x_2730_; size_t v___x_2731_; size_t v___x_2732_; lean_object* v_bkt_2733_; uint8_t v___x_2734_; 
v___x_2722_ = 32ULL;
v___x_2723_ = lean_uint64_shift_right(v___y_2721_, v___x_2722_);
v_fold_2724_ = lean_uint64_xor(v___y_2721_, v___x_2723_);
v___x_2725_ = 16ULL;
v___x_2726_ = lean_uint64_shift_right(v_fold_2724_, v___x_2725_);
v___x_2727_ = lean_uint64_xor(v_fold_2724_, v___x_2726_);
v___x_2728_ = lean_uint64_to_usize(v___x_2727_);
v___x_2729_ = lean_usize_of_nat(v___x_2719_);
v___x_2730_ = ((size_t)1ULL);
v___x_2731_ = lean_usize_sub(v___x_2729_, v___x_2730_);
v___x_2732_ = lean_usize_land(v___x_2728_, v___x_2731_);
v_bkt_2733_ = lean_array_uget_borrowed(v_buckets_2715_, v___x_2732_);
v___x_2734_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_2712_, v_bkt_2733_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2735_; lean_object* v_size_x27_2736_; lean_object* v___x_2737_; lean_object* v_buckets_x27_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; uint8_t v___x_2744_; 
v___x_2735_ = lean_unsigned_to_nat(1u);
v_size_x27_2736_ = lean_nat_add(v_size_2714_, v___x_2735_);
lean_dec(v_size_2714_);
lean_inc(v_bkt_2733_);
v___x_2737_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2737_, 0, v_a_2712_);
lean_ctor_set(v___x_2737_, 1, v_b_2713_);
lean_ctor_set(v___x_2737_, 2, v_bkt_2733_);
v_buckets_x27_2738_ = lean_array_uset(v_buckets_2715_, v___x_2732_, v___x_2737_);
v___x_2739_ = lean_unsigned_to_nat(4u);
v___x_2740_ = lean_nat_mul(v_size_x27_2736_, v___x_2739_);
v___x_2741_ = lean_unsigned_to_nat(3u);
v___x_2742_ = lean_nat_div(v___x_2740_, v___x_2741_);
lean_dec(v___x_2740_);
v___x_2743_ = lean_array_get_size(v_buckets_x27_2738_);
v___x_2744_ = lean_nat_dec_le(v___x_2742_, v___x_2743_);
lean_dec(v___x_2742_);
if (v___x_2744_ == 0)
{
lean_object* v_val_2745_; lean_object* v___x_2747_; 
v_val_2745_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6___redArg(v_buckets_x27_2738_);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 1, v_val_2745_);
lean_ctor_set(v___x_2717_, 0, v_size_x27_2736_);
v___x_2747_ = v___x_2717_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_size_x27_2736_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v_val_2745_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
else
{
lean_object* v___x_2750_; 
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 1, v_buckets_x27_2738_);
lean_ctor_set(v___x_2717_, 0, v_size_x27_2736_);
v___x_2750_ = v___x_2717_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_size_x27_2736_);
lean_ctor_set(v_reuseFailAlloc_2751_, 1, v_buckets_x27_2738_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
else
{
lean_object* v___x_2752_; lean_object* v_buckets_x27_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2757_; 
lean_inc(v_bkt_2733_);
v___x_2752_ = lean_box(0);
v_buckets_x27_2753_ = lean_array_uset(v_buckets_2715_, v___x_2732_, v___x_2752_);
v___x_2754_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7___redArg(v_a_2712_, v_b_2713_, v_bkt_2733_);
v___x_2755_ = lean_array_uset(v_buckets_x27_2753_, v___x_2732_, v___x_2754_);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 1, v___x_2755_);
v___x_2757_ = v___x_2717_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_size_2714_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v___x_2755_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2765_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__2));
v___x_2766_ = lean_unsigned_to_nat(4u);
v___x_2767_ = lean_unsigned_to_nat(238u);
v___x_2768_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__1));
v___x_2769_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__0));
v___x_2770_ = l_mkPanicMessageWithDecl(v___x_2769_, v___x_2768_, v___x_2767_, v___x_2766_, v___x_2765_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg(lean_object* v___x_2771_, lean_object* v_as_x27_2772_, lean_object* v_b_2773_){
_start:
{
if (lean_obj_tag(v_as_x27_2772_) == 0)
{
return v_b_2773_;
}
else
{
lean_object* v_head_2774_; lean_object* v_tail_2775_; lean_object* v_fst_2776_; lean_object* v_snd_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2798_; 
v_head_2774_ = lean_ctor_get(v_as_x27_2772_, 0);
v_tail_2775_ = lean_ctor_get(v_as_x27_2772_, 1);
v_fst_2776_ = lean_ctor_get(v_b_2773_, 0);
v_snd_2777_ = lean_ctor_get(v_b_2773_, 1);
v_isSharedCheck_2798_ = !lean_is_exclusive(v_b_2773_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2779_ = v_b_2773_;
v_isShared_2780_ = v_isSharedCheck_2798_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_snd_2777_);
lean_inc(v_fst_2776_);
lean_dec(v_b_2773_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2798_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v_map_2782_; uint8_t v___x_2796_; 
v___x_2796_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg(v___x_2771_, v_head_2774_);
if (v___x_2796_ == 0)
{
v_map_2782_ = v_fst_2776_;
goto v___jp_2781_;
}
else
{
lean_object* v___x_2797_; 
lean_inc(v_snd_2777_);
lean_inc(v_head_2774_);
v___x_2797_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3___redArg(v_fst_2776_, v_head_2774_, v_snd_2777_);
v_map_2782_ = v___x_2797_;
goto v___jp_2781_;
}
v___jp_2781_:
{
lean_object* v___x_2783_; uint8_t v___x_2784_; 
v___x_2783_ = lean_unsigned_to_nat(0u);
v___x_2784_ = lean_nat_dec_eq(v_snd_2777_, v___x_2783_);
if (v___x_2784_ == 0)
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2788_; 
v___x_2785_ = lean_unsigned_to_nat(1u);
v___x_2786_ = lean_nat_sub(v_snd_2777_, v___x_2785_);
lean_dec(v_snd_2777_);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 1, v___x_2786_);
lean_ctor_set(v___x_2779_, 0, v_map_2782_);
v___x_2788_ = v___x_2779_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_map_2782_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
v_as_x27_2772_ = v_tail_2775_;
v_b_2773_ = v___x_2788_;
goto _start;
}
}
else
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
lean_dec_ref(v_map_2782_);
lean_del_object(v___x_2779_);
lean_dec(v_snd_2777_);
v___x_2791_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3);
v___x_2792_ = l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1(v___x_2791_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2793_);
lean_dec_ref_known(v___x_2792_, 1);
return v_a_2793_;
}
else
{
lean_object* v_a_2794_; 
v_a_2794_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2794_);
lean_dec_ref_known(v___x_2792_, 1);
v_as_x27_2772_ = v_tail_2775_;
v_b_2773_ = v_a_2794_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___boxed(lean_object* v___x_2799_, lean_object* v_as_x27_2800_, lean_object* v_b_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg(v___x_2799_, v_as_x27_2800_, v_b_2801_);
lean_dec(v_as_x27_2800_);
lean_dec_ref(v___x_2799_);
return v_res_2802_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0(void){
_start:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2803_ = lean_box(0);
v___x_2804_ = lean_unsigned_to_nat(16u);
v___x_2805_ = lean_mk_array(v___x_2804_, v___x_2803_);
return v___x_2805_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1(void){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2806_ = lean_obj_once(&l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0, &l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0_once, _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0);
v___x_2807_ = lean_unsigned_to_nat(0u);
v___x_2808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
lean_ctor_set(v___x_2808_, 1, v___x_2806_);
return v___x_2808_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3(void){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2810_ = ((lean_object*)(l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__2));
v___x_2811_ = lean_unsigned_to_nat(2u);
v___x_2812_ = lean_unsigned_to_nat(240u);
v___x_2813_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__1));
v___x_2814_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__0));
v___x_2815_ = l_mkPanicMessageWithDecl(v___x_2814_, v___x_2813_, v___x_2812_, v___x_2811_, v___x_2810_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureDeclIndices(lean_object* v_env_2816_, lean_object* v_targets_2817_){
_start:
{
lean_object* v___x_2818_; lean_object* v_asyncMode_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v_fst_2823_; lean_object* v_snd_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2853_; 
v___x_2818_ = l_Lean_Compiler_LCNF_declOrderExt;
v_asyncMode_2819_ = lean_ctor_get(v___x_2818_, 2);
v___x_2820_ = ((lean_object*)(l_Lean_Compiler_LCNF_isDeclTransparent___closed__0));
v___x_2821_ = lean_box(0);
v___x_2822_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2820_, v___x_2818_, v_env_2816_, v_asyncMode_2819_, v___x_2821_);
v_fst_2823_ = lean_ctor_get(v___x_2822_, 0);
v_snd_2824_ = lean_ctor_get(v___x_2822_, 1);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2826_ = v___x_2822_;
v_isShared_2827_ = v_isSharedCheck_2853_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_snd_2824_);
lean_inc(v_fst_2823_);
lean_dec(v___x_2822_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2853_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___y_2829_; 
if (lean_obj_tag(v_snd_2824_) == 0)
{
lean_object* v_size_2851_; 
v_size_2851_ = lean_ctor_get(v_snd_2824_, 0);
lean_inc(v_size_2851_);
lean_dec_ref_known(v_snd_2824_, 5);
v___y_2829_ = v_size_2851_;
goto v___jp_2828_;
}
else
{
lean_object* v___x_2852_; 
v___x_2852_ = lean_unsigned_to_nat(0u);
v___y_2829_ = v___x_2852_;
goto v___jp_2828_;
}
v___jp_2828_:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v_map_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2842_; 
v___x_2830_ = lean_unsigned_to_nat(0u);
v___x_2831_ = lean_unsigned_to_nat(4u);
v___x_2832_ = lean_nat_mul(v___y_2829_, v___x_2831_);
v___x_2833_ = lean_unsigned_to_nat(3u);
v___x_2834_ = lean_nat_div(v___x_2832_, v___x_2833_);
lean_dec(v___x_2832_);
v___x_2835_ = l_Nat_nextPowerOfTwo(v___x_2834_);
lean_dec(v___x_2834_);
v___x_2836_ = lean_box(0);
v___x_2837_ = lean_mk_array(v___x_2835_, v___x_2836_);
v_map_2838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_map_2838_, 0, v___x_2830_);
lean_ctor_set(v_map_2838_, 1, v___x_2837_);
v___x_2839_ = lean_obj_once(&l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1, &l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1_once, _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1);
v___x_2840_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0(v___x_2839_, v_targets_2817_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 1, v___y_2829_);
lean_ctor_set(v___x_2826_, 0, v_map_2838_);
v___x_2842_ = v___x_2826_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_map_2838_);
lean_ctor_set(v_reuseFailAlloc_2850_, 1, v___y_2829_);
v___x_2842_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
lean_object* v___x_2843_; lean_object* v_fst_2844_; lean_object* v_size_2845_; lean_object* v___x_2846_; uint8_t v___x_2847_; 
v___x_2843_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg(v___x_2840_, v_fst_2823_, v___x_2842_);
lean_dec(v_fst_2823_);
lean_dec_ref(v___x_2840_);
v_fst_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_fst_2844_);
lean_dec_ref(v___x_2843_);
v_size_2845_ = lean_ctor_get(v_fst_2844_, 0);
v___x_2846_ = lean_array_get_size(v_targets_2817_);
v___x_2847_ = lean_nat_dec_eq(v_size_2845_, v___x_2846_);
if (v___x_2847_ == 0)
{
lean_object* v___x_2848_; lean_object* v___x_2849_; 
lean_dec(v_fst_2844_);
v___x_2848_ = lean_obj_once(&l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3, &l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3_once, _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3);
v___x_2849_ = l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__5(v___x_2848_);
return v___x_2849_;
}
else
{
return v_fst_2844_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureDeclIndices___boxed(lean_object* v_env_2854_, lean_object* v_targets_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_Lean_Compiler_LCNF_getImpureDeclIndices(v_env_2854_, v_targets_2855_);
lean_dec_ref(v_targets_2855_);
return v_res_2856_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2(lean_object* v_00_u03b2_2857_, lean_object* v_m_2858_, lean_object* v_a_2859_){
_start:
{
uint8_t v___x_2860_; 
v___x_2860_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg(v_m_2858_, v_a_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___boxed(lean_object* v_00_u03b2_2861_, lean_object* v_m_2862_, lean_object* v_a_2863_){
_start:
{
uint8_t v_res_2864_; lean_object* v_r_2865_; 
v_res_2864_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2(v_00_u03b2_2861_, v_m_2862_, v_a_2863_);
lean_dec(v_a_2863_);
lean_dec_ref(v_m_2862_);
v_r_2865_ = lean_box(v_res_2864_);
return v_r_2865_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3(lean_object* v_00_u03b2_2866_, lean_object* v_m_2867_, lean_object* v_a_2868_, lean_object* v_b_2869_){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3___redArg(v_m_2867_, v_a_2868_, v_b_2869_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4(lean_object* v___x_2871_, lean_object* v_as_2872_, lean_object* v_as_x27_2873_, lean_object* v_b_2874_, lean_object* v_a_2875_){
_start:
{
lean_object* v___x_2876_; 
v___x_2876_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg(v___x_2871_, v_as_x27_2873_, v_b_2874_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___boxed(lean_object* v___x_2877_, lean_object* v_as_2878_, lean_object* v_as_x27_2879_, lean_object* v_b_2880_, lean_object* v_a_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4(v___x_2877_, v_as_2878_, v_as_x27_2879_, v_b_2880_, v_a_2881_);
lean_dec(v_as_x27_2879_);
lean_dec(v_as_2878_);
lean_dec_ref(v___x_2877_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__0(lean_object* v_00_u03b2_2883_, lean_object* v_m_2884_, lean_object* v_a_2885_, lean_object* v_b_2886_){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__0___redArg(v_m_2884_, v_a_2885_, v_b_2886_);
return v___x_2887_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4(lean_object* v_00_u03b2_2888_, lean_object* v_a_2889_, lean_object* v_x_2890_){
_start:
{
uint8_t v___x_2891_; 
v___x_2891_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_2889_, v_x_2890_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2892_, lean_object* v_a_2893_, lean_object* v_x_2894_){
_start:
{
uint8_t v_res_2895_; lean_object* v_r_2896_; 
v_res_2895_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4(v_00_u03b2_2892_, v_a_2893_, v_x_2894_);
lean_dec(v_x_2894_);
lean_dec(v_a_2893_);
v_r_2896_ = lean_box(v_res_2895_);
return v_r_2896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6(lean_object* v_00_u03b2_2897_, lean_object* v_data_2898_){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6___redArg(v_data_2898_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7(lean_object* v_00_u03b2_2900_, lean_object* v_a_2901_, lean_object* v_b_2902_, lean_object* v_x_2903_){
_start:
{
lean_object* v___x_2904_; 
v___x_2904_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7___redArg(v_a_2901_, v_b_2902_, v_x_2903_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_2905_, lean_object* v_i_2906_, lean_object* v_source_2907_, lean_object* v_target_2908_){
_start:
{
lean_object* v___x_2909_; 
v___x_2909_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8___redArg(v_i_2906_, v_source_2907_, v_target_2908_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_2910_, lean_object* v_x_2911_, lean_object* v_x_2912_){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8_spec__10___redArg(v_x_2911_, v_x_2912_);
return v___x_2913_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PublicDeclsExt(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PublicDeclsExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3496178540____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_baseTransparentDeclsExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_baseTransparentDeclsExt);
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1977385844____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_monoTransparentDeclsExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_monoTransparentDeclsExt);
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_975450157____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_impureTransparentDeclsExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_impureTransparentDeclsExt);
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_baseExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_baseExt);
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_monoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_monoExt);
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_impureExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_impureExt);
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_impureSigExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_impureSigExt);
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_declOrderExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_declOrderExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Compiler_LCNF_mkDeclExt___auto__1 = _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkDeclExt___auto__1);
l_Lean_Compiler_LCNF_mkSigDeclExt___auto__1 = _init_l_Lean_Compiler_LCNF_mkSigDeclExt___auto__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkSigDeclExt___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PublicDeclsExt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PublicDeclsExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
}
#ifdef __cplusplus
}
#endif
