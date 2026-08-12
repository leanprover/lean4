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
lean_object* l_Lean_instInhabitedEnvExtension_default(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_Compiler_LCNF_isDeclPublic(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedDecl_default(uint8_t);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedSignature_default(uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__0_value),((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__0_value),((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__3_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__4;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__0_value),((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__0_value),((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__3_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__4;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0_value;
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
static lean_once_cell_t l_Lean_Compiler_LCNF_mkSigDeclExt___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___closed__7;
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
static const lean_closure_object l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2;
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
static lean_once_cell_t l_Lean_Compiler_LCNF_getSigCore_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getSigCore_x3f___closed__0;
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
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2;
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
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "Internal compiler error: getDecl\? on impure is unuspported for now"};
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(lean_object* v_f_96_, lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
if (lean_obj_tag(v_x_97_) == 0)
{
lean_object* v_es_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v_es_99_ = lean_ctor_get(v_x_97_, 0);
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = lean_array_get_size(v_es_99_);
v___x_102_ = lean_nat_dec_lt(v___x_100_, v___x_101_);
if (v___x_102_ == 0)
{
lean_dec(v_f_96_);
return v_x_98_;
}
else
{
uint8_t v___x_103_; 
v___x_103_ = lean_nat_dec_le(v___x_101_, v___x_101_);
if (v___x_103_ == 0)
{
if (v___x_102_ == 0)
{
lean_dec(v_f_96_);
return v_x_98_;
}
else
{
size_t v___x_104_; size_t v___x_105_; lean_object* v___x_106_; 
v___x_104_ = ((size_t)0ULL);
v___x_105_ = lean_usize_of_nat(v___x_101_);
v___x_106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg(v_f_96_, v_es_99_, v___x_104_, v___x_105_, v_x_98_);
return v___x_106_;
}
}
else
{
size_t v___x_107_; size_t v___x_108_; lean_object* v___x_109_; 
v___x_107_ = ((size_t)0ULL);
v___x_108_ = lean_usize_of_nat(v___x_101_);
v___x_109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg(v_f_96_, v_es_99_, v___x_107_, v___x_108_, v_x_98_);
return v___x_109_;
}
}
}
else
{
lean_object* v_ks_110_; lean_object* v_vs_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v_ks_110_ = lean_ctor_get(v_x_97_, 0);
v_vs_111_ = lean_ctor_get(v_x_97_, 1);
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___redArg(v_f_96_, v_ks_110_, v_vs_111_, v___x_112_, v_x_98_);
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_114_, lean_object* v_as_115_, size_t v_i_116_, size_t v_stop_117_, lean_object* v_b_118_){
_start:
{
lean_object* v___y_120_; uint8_t v___x_124_; 
v___x_124_ = lean_usize_dec_eq(v_i_116_, v_stop_117_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; 
v___x_125_ = lean_array_uget_borrowed(v_as_115_, v_i_116_);
switch(lean_obj_tag(v___x_125_))
{
case 0:
{
lean_object* v_key_126_; lean_object* v_val_127_; lean_object* v___x_128_; 
v_key_126_ = lean_ctor_get(v___x_125_, 0);
v_val_127_ = lean_ctor_get(v___x_125_, 1);
lean_inc(v_f_114_);
lean_inc(v_val_127_);
lean_inc(v_key_126_);
v___x_128_ = lean_apply_3(v_f_114_, v_b_118_, v_key_126_, v_val_127_);
v___y_120_ = v___x_128_;
goto v___jp_119_;
}
case 1:
{
lean_object* v_node_129_; lean_object* v___x_130_; 
v_node_129_ = lean_ctor_get(v___x_125_, 0);
lean_inc(v_f_114_);
v___x_130_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v_f_114_, v_node_129_, v_b_118_);
v___y_120_ = v___x_130_;
goto v___jp_119_;
}
default: 
{
v___y_120_ = v_b_118_;
goto v___jp_119_;
}
}
}
else
{
lean_dec(v_f_114_);
return v_b_118_;
}
v___jp_119_:
{
size_t v___x_121_; size_t v___x_122_; 
v___x_121_ = ((size_t)1ULL);
v___x_122_ = lean_usize_add(v_i_116_, v___x_121_);
v_i_116_ = v___x_122_;
v_b_118_ = v___y_120_;
goto _start;
}
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_139_, lean_object* v_x_140_, lean_object* v_x_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v_f_139_, v_x_140_, v_x_141_);
lean_dec_ref(v_x_140_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg___lam__0(lean_object* v_f_143_, lean_object* v_x1_144_, lean_object* v_x2_145_, lean_object* v_x3_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = lean_apply_3(v_f_143_, v_x1_144_, v_x2_145_, v_x3_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(lean_object* v_map_148_, lean_object* v_f_149_, lean_object* v_init_150_){
_start:
{
lean_object* v___f_151_; lean_object* v___x_152_; 
v___f_151_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_151_, 0, v_f_149_);
v___x_152_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v___f_151_, v_map_148_, v_init_150_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg___boxed(lean_object* v_map_153_, lean_object* v_f_154_, lean_object* v_init_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_map_153_, v_f_154_, v_init_155_);
lean_dec_ref(v_map_153_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2___redArg(lean_object* v_lt_157_, lean_object* v_hi_158_, lean_object* v_pivot_159_, lean_object* v_as_160_, lean_object* v_i_161_, lean_object* v_k_162_){
_start:
{
uint8_t v___x_163_; 
v___x_163_ = lean_nat_dec_lt(v_k_162_, v_hi_158_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; 
lean_dec(v_k_162_);
lean_dec(v_pivot_159_);
lean_dec_ref(v_lt_157_);
v___x_164_ = lean_array_fswap(v_as_160_, v_i_161_, v_hi_158_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v_i_161_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
return v___x_165_;
}
else
{
lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_166_ = lean_array_fget_borrowed(v_as_160_, v_k_162_);
lean_inc_ref(v_lt_157_);
lean_inc(v_pivot_159_);
lean_inc(v___x_166_);
v___x_167_ = lean_apply_2(v_lt_157_, v___x_166_, v_pivot_159_);
v___x_168_ = lean_unbox(v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_unsigned_to_nat(1u);
v___x_170_ = lean_nat_add(v_k_162_, v___x_169_);
lean_dec(v_k_162_);
v_k_162_ = v___x_170_;
goto _start;
}
else
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_172_ = lean_array_fswap(v_as_160_, v_i_161_, v_k_162_);
v___x_173_ = lean_unsigned_to_nat(1u);
v___x_174_ = lean_nat_add(v_i_161_, v___x_173_);
lean_dec(v_i_161_);
v___x_175_ = lean_nat_add(v_k_162_, v___x_173_);
lean_dec(v_k_162_);
v_as_160_ = v___x_172_;
v_i_161_ = v___x_174_;
v_k_162_ = v___x_175_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2___redArg___boxed(lean_object* v_lt_177_, lean_object* v_hi_178_, lean_object* v_pivot_179_, lean_object* v_as_180_, lean_object* v_i_181_, lean_object* v_k_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2___redArg(v_lt_177_, v_hi_178_, v_pivot_179_, v_as_180_, v_i_181_, v_k_182_);
lean_dec(v_hi_178_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(lean_object* v_lt_184_, lean_object* v_n_185_, lean_object* v_as_186_, lean_object* v_lo_187_, lean_object* v_hi_188_){
_start:
{
lean_object* v___y_190_; uint8_t v___x_200_; 
v___x_200_ = lean_nat_dec_lt(v_lo_187_, v_hi_188_);
if (v___x_200_ == 0)
{
lean_dec(v_lo_187_);
lean_dec_ref(v_lt_184_);
return v_as_186_;
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v_mid_203_; lean_object* v___y_205_; lean_object* v___y_212_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_201_ = lean_nat_add(v_lo_187_, v_hi_188_);
v___x_202_ = lean_unsigned_to_nat(1u);
v_mid_203_ = lean_nat_shiftr(v___x_201_, v___x_202_);
lean_dec(v___x_201_);
v___x_218_ = lean_array_fget_borrowed(v_as_186_, v_mid_203_);
v___x_219_ = lean_array_fget_borrowed(v_as_186_, v_lo_187_);
lean_inc_ref(v_lt_184_);
lean_inc(v___x_219_);
lean_inc(v___x_218_);
v___x_220_ = lean_apply_2(v_lt_184_, v___x_218_, v___x_219_);
v___x_221_ = lean_unbox(v___x_220_);
if (v___x_221_ == 0)
{
v___y_212_ = v_as_186_;
goto v___jp_211_;
}
else
{
lean_object* v___x_222_; 
v___x_222_ = lean_array_fswap(v_as_186_, v_lo_187_, v_mid_203_);
v___y_212_ = v___x_222_;
goto v___jp_211_;
}
v___jp_204_:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_206_ = lean_array_fget_borrowed(v___y_205_, v_mid_203_);
v___x_207_ = lean_array_fget_borrowed(v___y_205_, v_hi_188_);
lean_inc_ref(v_lt_184_);
lean_inc(v___x_207_);
lean_inc(v___x_206_);
v___x_208_ = lean_apply_2(v_lt_184_, v___x_206_, v___x_207_);
v___x_209_ = lean_unbox(v___x_208_);
if (v___x_209_ == 0)
{
lean_dec(v_mid_203_);
v___y_190_ = v___y_205_;
goto v___jp_189_;
}
else
{
lean_object* v___x_210_; 
v___x_210_ = lean_array_fswap(v___y_205_, v_mid_203_, v_hi_188_);
lean_dec(v_mid_203_);
v___y_190_ = v___x_210_;
goto v___jp_189_;
}
}
v___jp_211_:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_213_ = lean_array_fget_borrowed(v___y_212_, v_hi_188_);
v___x_214_ = lean_array_fget_borrowed(v___y_212_, v_lo_187_);
lean_inc_ref(v_lt_184_);
lean_inc(v___x_214_);
lean_inc(v___x_213_);
v___x_215_ = lean_apply_2(v_lt_184_, v___x_213_, v___x_214_);
v___x_216_ = lean_unbox(v___x_215_);
if (v___x_216_ == 0)
{
v___y_205_ = v___y_212_;
goto v___jp_204_;
}
else
{
lean_object* v___x_217_; 
v___x_217_ = lean_array_fswap(v___y_212_, v_lo_187_, v_hi_188_);
v___y_205_ = v___x_217_;
goto v___jp_204_;
}
}
}
v___jp_189_:
{
lean_object* v_pivot_191_; lean_object* v___x_192_; lean_object* v_fst_193_; lean_object* v_snd_194_; uint8_t v___x_195_; 
v_pivot_191_ = lean_array_fget(v___y_190_, v_hi_188_);
lean_inc_n(v_lo_187_, 2);
lean_inc_ref(v_lt_184_);
v___x_192_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2___redArg(v_lt_184_, v_hi_188_, v_pivot_191_, v___y_190_, v_lo_187_, v_lo_187_);
v_fst_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_fst_193_);
v_snd_194_ = lean_ctor_get(v___x_192_, 1);
lean_inc(v_snd_194_);
lean_dec_ref(v___x_192_);
v___x_195_ = lean_nat_dec_le(v_hi_188_, v_fst_193_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
lean_inc_ref(v_lt_184_);
v___x_196_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_184_, v_n_185_, v_snd_194_, v_lo_187_, v_fst_193_);
v___x_197_ = lean_unsigned_to_nat(1u);
v___x_198_ = lean_nat_add(v_fst_193_, v___x_197_);
lean_dec(v_fst_193_);
v_as_186_ = v___x_196_;
v_lo_187_ = v___x_198_;
goto _start;
}
else
{
lean_dec(v_fst_193_);
lean_dec(v_lo_187_);
lean_dec_ref(v_lt_184_);
return v_snd_194_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg___boxed(lean_object* v_lt_223_, lean_object* v_n_224_, lean_object* v_as_225_, lean_object* v_lo_226_, lean_object* v_hi_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_223_, v_n_224_, v_as_225_, v_lo_226_, v_hi_227_);
lean_dec(v_hi_227_);
lean_dec(v_n_224_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(lean_object* v_s_232_, lean_object* v_lt_233_){
_start:
{
lean_object* v___f_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v_decls_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v___f_234_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__0));
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__1));
v_decls_237_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_s_232_, v___f_234_, v___x_236_);
v___x_238_ = lean_array_get_size(v_decls_237_);
v___x_239_ = lean_nat_dec_eq(v___x_238_, v___x_235_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___y_243_; uint8_t v___x_247_; 
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = lean_nat_sub(v___x_238_, v___x_240_);
v___x_247_ = lean_nat_dec_le(v___x_235_, v___x_241_);
if (v___x_247_ == 0)
{
lean_inc(v___x_241_);
v___y_243_ = v___x_241_;
goto v___jp_242_;
}
else
{
v___y_243_ = v___x_235_;
goto v___jp_242_;
}
v___jp_242_:
{
uint8_t v___x_244_; 
v___x_244_ = lean_nat_dec_le(v___y_243_, v___x_241_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; 
lean_dec(v___x_241_);
lean_inc(v___y_243_);
v___x_245_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_233_, v___x_238_, v_decls_237_, v___y_243_, v___y_243_);
lean_dec(v___y_243_);
return v___x_245_;
}
else
{
lean_object* v___x_246_; 
v___x_246_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_233_, v___x_238_, v_decls_237_, v___y_243_, v___x_241_);
lean_dec(v___x_241_);
return v___x_246_;
}
}
}
else
{
lean_dec_ref(v_lt_233_);
return v_decls_237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___boxed(lean_object* v_s_248_, lean_object* v_lt_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(v_s_248_, v_lt_249_);
lean_dec_ref(v_s_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries(uint8_t v_pu_251_, lean_object* v_00_u03b2_252_, lean_object* v_s_253_, lean_object* v_lt_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(v_s_253_, v_lt_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___boxed(lean_object* v_pu_256_, lean_object* v_00_u03b2_257_, lean_object* v_s_258_, lean_object* v_lt_259_){
_start:
{
uint8_t v_pu_boxed_260_; lean_object* v_res_261_; 
v_pu_boxed_260_ = lean_unbox(v_pu_256_);
v_res_261_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries(v_pu_boxed_260_, v_00_u03b2_257_, v_s_258_, v_lt_259_);
lean_dec_ref(v_s_258_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0(lean_object* v_00_u03c3_262_, lean_object* v_00_u03b2_263_, lean_object* v_map_264_, lean_object* v_f_265_, lean_object* v_init_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_map_264_, v_f_265_, v_init_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___boxed(lean_object* v_00_u03c3_268_, lean_object* v_00_u03b2_269_, lean_object* v_map_270_, lean_object* v_f_271_, lean_object* v_init_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0(v_00_u03c3_268_, v_00_u03b2_269_, v_map_270_, v_f_271_, v_init_272_);
lean_dec_ref(v_map_270_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1(lean_object* v_00_u03b2_274_, lean_object* v_lt_275_, lean_object* v_n_276_, lean_object* v_as_277_, lean_object* v_lo_278_, lean_object* v_hi_279_, lean_object* v_w_280_, lean_object* v_hlo_281_, lean_object* v_hhi_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_275_, v_n_276_, v_as_277_, v_lo_278_, v_hi_279_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___boxed(lean_object* v_00_u03b2_284_, lean_object* v_lt_285_, lean_object* v_n_286_, lean_object* v_as_287_, lean_object* v_lo_288_, lean_object* v_hi_289_, lean_object* v_w_290_, lean_object* v_hlo_291_, lean_object* v_hhi_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1(v_00_u03b2_284_, v_lt_285_, v_n_286_, v_as_287_, v_lo_288_, v_hi_289_, v_w_290_, v_hlo_291_, v_hhi_292_);
lean_dec(v_hi_289_);
lean_dec(v_n_286_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___redArg(lean_object* v_map_294_, lean_object* v_f_295_, lean_object* v_init_296_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v_f_295_, v_map_294_, v_init_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___redArg___boxed(lean_object* v_map_298_, lean_object* v_f_299_, lean_object* v_init_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___redArg(v_map_298_, v_f_299_, v_init_300_);
lean_dec_ref(v_map_298_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0(lean_object* v_00_u03c3_302_, lean_object* v_00_u03b2_303_, lean_object* v_map_304_, lean_object* v_f_305_, lean_object* v_init_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v_f_305_, v_map_304_, v_init_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___boxed(lean_object* v_00_u03c3_308_, lean_object* v_00_u03b2_309_, lean_object* v_map_310_, lean_object* v_f_311_, lean_object* v_init_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0(v_00_u03c3_308_, v_00_u03b2_309_, v_map_310_, v_f_311_, v_init_312_);
lean_dec_ref(v_map_310_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2(lean_object* v_00_u03b2_314_, lean_object* v_lt_315_, lean_object* v_n_316_, lean_object* v_lo_317_, lean_object* v_hi_318_, lean_object* v_hhi_319_, lean_object* v_pivot_320_, lean_object* v_as_321_, lean_object* v_i_322_, lean_object* v_k_323_, lean_object* v_ilo_324_, lean_object* v_ik_325_, lean_object* v_w_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2___redArg(v_lt_315_, v_hi_318_, v_pivot_320_, v_as_321_, v_i_322_, v_k_323_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2___boxed(lean_object* v_00_u03b2_328_, lean_object* v_lt_329_, lean_object* v_n_330_, lean_object* v_lo_331_, lean_object* v_hi_332_, lean_object* v_hhi_333_, lean_object* v_pivot_334_, lean_object* v_as_335_, lean_object* v_i_336_, lean_object* v_k_337_, lean_object* v_ilo_338_, lean_object* v_ik_339_, lean_object* v_w_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2(v_00_u03b2_328_, v_lt_329_, v_n_330_, v_lo_331_, v_hi_332_, v_hhi_333_, v_pivot_334_, v_as_335_, v_i_336_, v_k_337_, v_ilo_338_, v_ik_339_, v_w_340_);
lean_dec(v_hi_332_);
lean_dec(v_lo_331_);
lean_dec(v_n_330_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_342_, lean_object* v_00_u03b1_343_, lean_object* v_00_u03b2_344_, lean_object* v_f_345_, lean_object* v_x_346_, lean_object* v_x_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v_f_345_, v_x_346_, v_x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_349_, lean_object* v_00_u03b1_350_, lean_object* v_00_u03b2_351_, lean_object* v_f_352_, lean_object* v_x_353_, lean_object* v_x_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1(v_00_u03c3_349_, v_00_u03b1_350_, v_00_u03b2_351_, v_f_352_, v_x_353_, v_x_354_);
lean_dec_ref(v_x_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_356_, lean_object* v_00_u03b2_357_, lean_object* v_00_u03c3_358_, lean_object* v_f_359_, lean_object* v_as_360_, size_t v_i_361_, size_t v_stop_362_, lean_object* v_b_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg(v_f_359_, v_as_360_, v_i_361_, v_stop_362_, v_b_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_365_, lean_object* v_00_u03b2_366_, lean_object* v_00_u03c3_367_, lean_object* v_f_368_, lean_object* v_as_369_, lean_object* v_i_370_, lean_object* v_stop_371_, lean_object* v_b_372_){
_start:
{
size_t v_i_boxed_373_; size_t v_stop_boxed_374_; lean_object* v_res_375_; 
v_i_boxed_373_ = lean_unbox_usize(v_i_370_);
lean_dec(v_i_370_);
v_stop_boxed_374_ = lean_unbox_usize(v_stop_371_);
lean_dec(v_stop_371_);
v_res_375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_365_, v_00_u03b2_366_, v_00_u03c3_367_, v_f_368_, v_as_369_, v_i_boxed_373_, v_stop_boxed_374_, v_b_372_);
lean_dec_ref(v_as_369_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03c3_376_, lean_object* v_00_u03b1_377_, lean_object* v_00_u03b2_378_, lean_object* v_f_379_, lean_object* v_keys_380_, lean_object* v_vals_381_, lean_object* v_heq_382_, lean_object* v_i_383_, lean_object* v_acc_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___redArg(v_f_379_, v_keys_380_, v_vals_381_, v_i_383_, v_acc_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03c3_386_, lean_object* v_00_u03b1_387_, lean_object* v_00_u03b2_388_, lean_object* v_f_389_, lean_object* v_keys_390_, lean_object* v_vals_391_, lean_object* v_heq_392_, lean_object* v_i_393_, lean_object* v_acc_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4(v_00_u03c3_386_, v_00_u03b1_387_, v_00_u03b2_388_, v_f_389_, v_keys_390_, v_vals_391_, v_heq_392_, v_i_393_, v_acc_394_);
lean_dec_ref(v_vals_391_);
lean_dec_ref(v_keys_390_);
return v_res_395_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_396_, lean_object* v_i_397_, lean_object* v_k_398_){
_start:
{
lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_399_ = lean_array_get_size(v_keys_396_);
v___x_400_ = lean_nat_dec_lt(v_i_397_, v___x_399_);
if (v___x_400_ == 0)
{
lean_dec(v_i_397_);
return v___x_400_;
}
else
{
lean_object* v_k_x27_401_; uint8_t v___x_402_; 
v_k_x27_401_ = lean_array_fget_borrowed(v_keys_396_, v_i_397_);
v___x_402_ = lean_name_eq(v_k_398_, v_k_x27_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_unsigned_to_nat(1u);
v___x_404_ = lean_nat_add(v_i_397_, v___x_403_);
lean_dec(v_i_397_);
v_i_397_ = v___x_404_;
goto _start;
}
else
{
lean_dec(v_i_397_);
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_406_, lean_object* v_i_407_, lean_object* v_k_408_){
_start:
{
uint8_t v_res_409_; lean_object* v_r_410_; 
v_res_409_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg(v_keys_406_, v_i_407_, v_k_408_);
lean_dec(v_k_408_);
lean_dec_ref(v_keys_406_);
v_r_410_ = lean_box(v_res_409_);
return v_r_410_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg(lean_object* v_x_411_, size_t v_x_412_, lean_object* v_x_413_){
_start:
{
if (lean_obj_tag(v_x_411_) == 0)
{
lean_object* v_es_414_; lean_object* v___x_415_; size_t v___x_416_; size_t v___x_417_; lean_object* v_j_418_; lean_object* v___x_419_; 
v_es_414_ = lean_ctor_get(v_x_411_, 0);
v___x_415_ = lean_box(2);
v___x_416_ = ((size_t)31ULL);
v___x_417_ = lean_usize_land(v_x_412_, v___x_416_);
v_j_418_ = lean_usize_to_nat(v___x_417_);
v___x_419_ = lean_array_get_borrowed(v___x_415_, v_es_414_, v_j_418_);
lean_dec(v_j_418_);
switch(lean_obj_tag(v___x_419_))
{
case 0:
{
lean_object* v_key_420_; uint8_t v___x_421_; 
v_key_420_ = lean_ctor_get(v___x_419_, 0);
v___x_421_ = lean_name_eq(v_x_413_, v_key_420_);
return v___x_421_;
}
case 1:
{
lean_object* v_node_422_; size_t v___x_423_; size_t v___x_424_; 
v_node_422_ = lean_ctor_get(v___x_419_, 0);
v___x_423_ = ((size_t)5ULL);
v___x_424_ = lean_usize_shift_right(v_x_412_, v___x_423_);
v_x_411_ = v_node_422_;
v_x_412_ = v___x_424_;
goto _start;
}
default: 
{
uint8_t v___x_426_; 
v___x_426_ = 0;
return v___x_426_;
}
}
}
else
{
lean_object* v_ks_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_ks_427_ = lean_ctor_get(v_x_411_, 0);
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_429_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg(v_ks_427_, v___x_428_, v_x_413_);
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___boxed(lean_object* v_x_430_, lean_object* v_x_431_, lean_object* v_x_432_){
_start:
{
size_t v_x_412__boxed_433_; uint8_t v_res_434_; lean_object* v_r_435_; 
v_x_412__boxed_433_ = lean_unbox_usize(v_x_431_);
lean_dec(v_x_431_);
v_res_434_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg(v_x_430_, v_x_412__boxed_433_, v_x_432_);
lean_dec(v_x_432_);
lean_dec_ref(v_x_430_);
v_r_435_ = lean_box(v_res_434_);
return v_r_435_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg(lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
uint64_t v___y_439_; 
if (lean_obj_tag(v_x_437_) == 0)
{
uint64_t v___x_442_; 
v___x_442_ = 1723ULL;
v___y_439_ = v___x_442_;
goto v___jp_438_;
}
else
{
uint64_t v_hash_443_; 
v_hash_443_ = lean_ctor_get_uint64(v_x_437_, sizeof(void*)*2);
v___y_439_ = v_hash_443_;
goto v___jp_438_;
}
v___jp_438_:
{
size_t v___x_440_; uint8_t v___x_441_; 
v___x_440_ = lean_uint64_to_usize(v___y_439_);
v___x_441_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg(v_x_436_, v___x_440_, v_x_437_);
return v___x_441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___boxed(lean_object* v_x_444_, lean_object* v_x_445_){
_start:
{
uint8_t v_res_446_; lean_object* v_r_447_; 
v_res_446_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg(v_x_444_, v_x_445_);
lean_dec(v_x_445_);
lean_dec_ref(v_x_444_);
v_r_447_ = lean_box(v_res_446_);
return v_r_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_, lean_object* v_x_451_){
_start:
{
lean_object* v_ks_452_; lean_object* v_vs_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_477_; 
v_ks_452_ = lean_ctor_get(v_x_448_, 0);
v_vs_453_ = lean_ctor_get(v_x_448_, 1);
v_isSharedCheck_477_ = !lean_is_exclusive(v_x_448_);
if (v_isSharedCheck_477_ == 0)
{
v___x_455_ = v_x_448_;
v_isShared_456_ = v_isSharedCheck_477_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_vs_453_);
lean_inc(v_ks_452_);
lean_dec(v_x_448_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_477_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = lean_array_get_size(v_ks_452_);
v___x_458_ = lean_nat_dec_lt(v_x_449_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
lean_dec(v_x_449_);
v___x_459_ = lean_array_push(v_ks_452_, v_x_450_);
v___x_460_ = lean_array_push(v_vs_453_, v_x_451_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v___x_460_);
lean_ctor_set(v___x_455_, 0, v___x_459_);
v___x_462_ = v___x_455_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
else
{
lean_object* v_k_x27_464_; uint8_t v___x_465_; 
v_k_x27_464_ = lean_array_fget_borrowed(v_ks_452_, v_x_449_);
v___x_465_ = lean_name_eq(v_x_450_, v_k_x27_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_467_; 
if (v_isShared_456_ == 0)
{
v___x_467_ = v___x_455_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_ks_452_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_vs_453_);
v___x_467_ = v_reuseFailAlloc_471_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_unsigned_to_nat(1u);
v___x_469_ = lean_nat_add(v_x_449_, v___x_468_);
lean_dec(v_x_449_);
v_x_448_ = v___x_467_;
v_x_449_ = v___x_469_;
goto _start;
}
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_472_ = lean_array_fset(v_ks_452_, v_x_449_, v_x_450_);
v___x_473_ = lean_array_fset(v_vs_453_, v_x_449_, v_x_451_);
lean_dec(v_x_449_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v___x_473_);
lean_ctor_set(v___x_455_, 0, v___x_472_);
v___x_475_ = v___x_455_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_472_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v___x_473_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4___redArg(lean_object* v_n_478_, lean_object* v_k_479_, lean_object* v_v_480_){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_unsigned_to_nat(0u);
v___x_482_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4_spec__5___redArg(v_n_478_, v___x_481_, v_k_479_, v_v_480_);
return v___x_482_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(lean_object* v_x_484_, size_t v_x_485_, size_t v_x_486_, lean_object* v_x_487_, lean_object* v_x_488_){
_start:
{
if (lean_obj_tag(v_x_484_) == 0)
{
lean_object* v_es_489_; size_t v___x_490_; size_t v___x_491_; lean_object* v_j_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v_es_489_ = lean_ctor_get(v_x_484_, 0);
v___x_490_ = ((size_t)31ULL);
v___x_491_ = lean_usize_land(v_x_485_, v___x_490_);
v_j_492_ = lean_usize_to_nat(v___x_491_);
v___x_493_ = lean_array_get_size(v_es_489_);
v___x_494_ = lean_nat_dec_lt(v_j_492_, v___x_493_);
if (v___x_494_ == 0)
{
lean_dec(v_j_492_);
lean_dec(v_x_488_);
lean_dec(v_x_487_);
return v_x_484_;
}
else
{
lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_533_; 
lean_inc_ref(v_es_489_);
v_isSharedCheck_533_ = !lean_is_exclusive(v_x_484_);
if (v_isSharedCheck_533_ == 0)
{
lean_object* v_unused_534_; 
v_unused_534_ = lean_ctor_get(v_x_484_, 0);
lean_dec(v_unused_534_);
v___x_496_ = v_x_484_;
v_isShared_497_ = v_isSharedCheck_533_;
goto v_resetjp_495_;
}
else
{
lean_dec(v_x_484_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_533_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v_v_498_; lean_object* v___x_499_; lean_object* v_xs_x27_500_; lean_object* v___y_502_; 
v_v_498_ = lean_array_fget(v_es_489_, v_j_492_);
v___x_499_ = lean_box(0);
v_xs_x27_500_ = lean_array_fset(v_es_489_, v_j_492_, v___x_499_);
switch(lean_obj_tag(v_v_498_))
{
case 0:
{
lean_object* v_key_507_; lean_object* v_val_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_518_; 
v_key_507_ = lean_ctor_get(v_v_498_, 0);
v_val_508_ = lean_ctor_get(v_v_498_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_v_498_);
if (v_isSharedCheck_518_ == 0)
{
v___x_510_ = v_v_498_;
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_val_508_);
lean_inc(v_key_507_);
lean_dec(v_v_498_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
uint8_t v___x_512_; 
v___x_512_ = lean_name_eq(v_x_487_, v_key_507_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; 
lean_del_object(v___x_510_);
v___x_513_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_507_, v_val_508_, v_x_487_, v_x_488_);
v___x_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
v___y_502_ = v___x_514_;
goto v___jp_501_;
}
else
{
lean_object* v___x_516_; 
lean_dec(v_val_508_);
lean_dec(v_key_507_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 1, v_x_488_);
lean_ctor_set(v___x_510_, 0, v_x_487_);
v___x_516_ = v___x_510_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_x_487_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_x_488_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
v___y_502_ = v___x_516_;
goto v___jp_501_;
}
}
}
}
case 1:
{
lean_object* v_node_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_531_; 
v_node_519_ = lean_ctor_get(v_v_498_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v_v_498_);
if (v_isSharedCheck_531_ == 0)
{
v___x_521_ = v_v_498_;
v_isShared_522_ = v_isSharedCheck_531_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_node_519_);
lean_dec(v_v_498_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_531_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
size_t v___x_523_; size_t v___x_524_; size_t v___x_525_; size_t v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_523_ = ((size_t)5ULL);
v___x_524_ = lean_usize_shift_right(v_x_485_, v___x_523_);
v___x_525_ = ((size_t)1ULL);
v___x_526_ = lean_usize_add(v_x_486_, v___x_525_);
v___x_527_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_node_519_, v___x_524_, v___x_526_, v_x_487_, v_x_488_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_527_);
v___x_529_ = v___x_521_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
v___y_502_ = v___x_529_;
goto v___jp_501_;
}
}
}
default: 
{
lean_object* v___x_532_; 
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v_x_487_);
lean_ctor_set(v___x_532_, 1, v_x_488_);
v___y_502_ = v___x_532_;
goto v___jp_501_;
}
}
v___jp_501_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = lean_array_fset(v_xs_x27_500_, v_j_492_, v___y_502_);
lean_dec(v_j_492_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_503_);
v___x_505_ = v___x_496_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
}
else
{
lean_object* v_ks_535_; lean_object* v_vs_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_556_; 
v_ks_535_ = lean_ctor_get(v_x_484_, 0);
v_vs_536_ = lean_ctor_get(v_x_484_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v_x_484_);
if (v_isSharedCheck_556_ == 0)
{
v___x_538_ = v_x_484_;
v_isShared_539_ = v_isSharedCheck_556_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_vs_536_);
lean_inc(v_ks_535_);
lean_dec(v_x_484_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_556_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_ks_535_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_vs_536_);
v___x_541_ = v_reuseFailAlloc_555_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v_newNode_542_; uint8_t v___y_544_; size_t v___x_550_; uint8_t v___x_551_; 
v_newNode_542_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4___redArg(v___x_541_, v_x_487_, v_x_488_);
v___x_550_ = ((size_t)7ULL);
v___x_551_ = lean_usize_dec_le(v___x_550_, v_x_486_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_552_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_542_);
v___x_553_ = lean_unsigned_to_nat(4u);
v___x_554_ = lean_nat_dec_lt(v___x_552_, v___x_553_);
lean_dec(v___x_552_);
v___y_544_ = v___x_554_;
goto v___jp_543_;
}
else
{
v___y_544_ = v___x_551_;
goto v___jp_543_;
}
v___jp_543_:
{
if (v___y_544_ == 0)
{
lean_object* v_ks_545_; lean_object* v_vs_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_ks_545_ = lean_ctor_get(v_newNode_542_, 0);
lean_inc_ref(v_ks_545_);
v_vs_546_ = lean_ctor_get(v_newNode_542_, 1);
lean_inc_ref(v_vs_546_);
lean_dec_ref(v_newNode_542_);
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0);
v___x_549_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg(v_x_486_, v_ks_545_, v_vs_546_, v___x_547_, v___x_548_);
lean_dec_ref(v_vs_546_);
lean_dec_ref(v_ks_545_);
return v___x_549_;
}
else
{
return v_newNode_542_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg(size_t v_depth_557_, lean_object* v_keys_558_, lean_object* v_vals_559_, lean_object* v_i_560_, lean_object* v_entries_561_){
_start:
{
lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_562_ = lean_array_get_size(v_keys_558_);
v___x_563_ = lean_nat_dec_lt(v_i_560_, v___x_562_);
if (v___x_563_ == 0)
{
lean_dec(v_i_560_);
return v_entries_561_;
}
else
{
lean_object* v_k_564_; lean_object* v_v_565_; uint64_t v___y_567_; 
v_k_564_ = lean_array_fget_borrowed(v_keys_558_, v_i_560_);
v_v_565_ = lean_array_fget_borrowed(v_vals_559_, v_i_560_);
if (lean_obj_tag(v_k_564_) == 0)
{
uint64_t v___x_578_; 
v___x_578_ = 1723ULL;
v___y_567_ = v___x_578_;
goto v___jp_566_;
}
else
{
uint64_t v_hash_579_; 
v_hash_579_ = lean_ctor_get_uint64(v_k_564_, sizeof(void*)*2);
v___y_567_ = v_hash_579_;
goto v___jp_566_;
}
v___jp_566_:
{
size_t v_h_568_; size_t v___x_569_; lean_object* v___x_570_; size_t v___x_571_; size_t v___x_572_; size_t v___x_573_; size_t v_h_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_h_568_ = lean_uint64_to_usize(v___y_567_);
v___x_569_ = ((size_t)5ULL);
v___x_570_ = lean_unsigned_to_nat(1u);
v___x_571_ = ((size_t)1ULL);
v___x_572_ = lean_usize_sub(v_depth_557_, v___x_571_);
v___x_573_ = lean_usize_mul(v___x_569_, v___x_572_);
v_h_574_ = lean_usize_shift_right(v_h_568_, v___x_573_);
v___x_575_ = lean_nat_add(v_i_560_, v___x_570_);
lean_dec(v_i_560_);
lean_inc(v_v_565_);
lean_inc(v_k_564_);
v___x_576_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_entries_561_, v_h_574_, v_depth_557_, v_k_564_, v_v_565_);
v_i_560_ = v___x_575_;
v_entries_561_ = v___x_576_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_580_, lean_object* v_keys_581_, lean_object* v_vals_582_, lean_object* v_i_583_, lean_object* v_entries_584_){
_start:
{
size_t v_depth_boxed_585_; lean_object* v_res_586_; 
v_depth_boxed_585_ = lean_unbox_usize(v_depth_580_);
lean_dec(v_depth_580_);
v_res_586_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg(v_depth_boxed_585_, v_keys_581_, v_vals_582_, v_i_583_, v_entries_584_);
lean_dec_ref(v_vals_582_);
lean_dec_ref(v_keys_581_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___boxed(lean_object* v_x_587_, lean_object* v_x_588_, lean_object* v_x_589_, lean_object* v_x_590_, lean_object* v_x_591_){
_start:
{
size_t v_x_547__boxed_592_; size_t v_x_548__boxed_593_; lean_object* v_res_594_; 
v_x_547__boxed_592_ = lean_unbox_usize(v_x_588_);
lean_dec(v_x_588_);
v_x_548__boxed_593_ = lean_unbox_usize(v_x_589_);
lean_dec(v_x_589_);
v_res_594_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_x_587_, v_x_547__boxed_592_, v_x_548__boxed_593_, v_x_590_, v_x_591_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(lean_object* v_x_595_, lean_object* v_x_596_, lean_object* v_x_597_){
_start:
{
uint64_t v___y_599_; 
if (lean_obj_tag(v_x_596_) == 0)
{
uint64_t v___x_603_; 
v___x_603_ = 1723ULL;
v___y_599_ = v___x_603_;
goto v___jp_598_;
}
else
{
uint64_t v_hash_604_; 
v_hash_604_ = lean_ctor_get_uint64(v_x_596_, sizeof(void*)*2);
v___y_599_ = v_hash_604_;
goto v___jp_598_;
}
v___jp_598_:
{
size_t v___x_600_; size_t v___x_601_; lean_object* v___x_602_; 
v___x_600_ = lean_uint64_to_usize(v___y_599_);
v___x_601_ = ((size_t)1ULL);
v___x_602_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_x_595_, v___x_600_, v___x_601_, v_x_596_, v_x_597_);
return v___x_602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___lam__0(lean_object* v_oldState_605_, lean_object* v_otherState_606_, lean_object* v_k_607_, lean_object* v_v_608_){
_start:
{
uint8_t v___x_609_; 
v___x_609_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg(v_oldState_605_, v_k_607_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_otherState_606_, v_k_607_, v_v_608_);
return v___x_610_;
}
else
{
lean_dec(v_v_608_);
lean_dec(v_k_607_);
return v_otherState_606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___lam__0___boxed(lean_object* v_oldState_611_, lean_object* v_otherState_612_, lean_object* v_k_613_, lean_object* v_v_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___lam__0(v_oldState_611_, v_otherState_612_, v_k_613_, v_v_614_);
lean_dec_ref(v_oldState_611_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg(lean_object* v_oldState_616_, lean_object* v_newState_617_, lean_object* v_otherState_618_){
_start:
{
lean_object* v___f_619_; lean_object* v___x_620_; 
v___f_619_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_619_, 0, v_oldState_616_);
v___x_620_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_newState_617_, v___f_619_, v_otherState_618_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___boxed(lean_object* v_oldState_621_, lean_object* v_newState_622_, lean_object* v_otherState_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg(v_oldState_621_, v_newState_622_, v_otherState_623_);
lean_dec_ref(v_newState_622_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn(lean_object* v_00_u03b2_625_, uint8_t v_phase_626_, lean_object* v_oldState_627_, lean_object* v_newState_628_, lean_object* v_x_629_, lean_object* v_otherState_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg(v_oldState_627_, v_newState_628_, v_otherState_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___boxed(lean_object* v_00_u03b2_632_, lean_object* v_phase_633_, lean_object* v_oldState_634_, lean_object* v_newState_635_, lean_object* v_x_636_, lean_object* v_otherState_637_){
_start:
{
uint8_t v_phase_boxed_638_; lean_object* v_res_639_; 
v_phase_boxed_638_ = lean_unbox(v_phase_633_);
v_res_639_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn(v_00_u03b2_632_, v_phase_boxed_638_, v_oldState_634_, v_newState_635_, v_x_636_, v_otherState_637_);
lean_dec(v_x_636_);
lean_dec_ref(v_newState_635_);
return v_res_639_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0(lean_object* v_00_u03b2_640_, lean_object* v_x_641_, lean_object* v_x_642_){
_start:
{
uint8_t v___x_643_; 
v___x_643_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg(v_x_641_, v_x_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___boxed(lean_object* v_00_u03b2_644_, lean_object* v_x_645_, lean_object* v_x_646_){
_start:
{
uint8_t v_res_647_; lean_object* v_r_648_; 
v_res_647_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0(v_00_u03b2_644_, v_x_645_, v_x_646_);
lean_dec(v_x_646_);
lean_dec_ref(v_x_645_);
v_r_648_ = lean_box(v_res_647_);
return v_r_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1(lean_object* v_00_u03b2_649_, lean_object* v_x_650_, lean_object* v_x_651_, lean_object* v_x_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_x_650_, v_x_651_, v_x_652_);
return v___x_653_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0(lean_object* v_00_u03b2_654_, lean_object* v_x_655_, size_t v_x_656_, lean_object* v_x_657_){
_start:
{
uint8_t v___x_658_; 
v___x_658_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg(v_x_655_, v_x_656_, v_x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___boxed(lean_object* v_00_u03b2_659_, lean_object* v_x_660_, lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
size_t v_x_752__boxed_663_; uint8_t v_res_664_; lean_object* v_r_665_; 
v_x_752__boxed_663_ = lean_unbox_usize(v_x_661_);
lean_dec(v_x_661_);
v_res_664_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0(v_00_u03b2_659_, v_x_660_, v_x_752__boxed_663_, v_x_662_);
lean_dec(v_x_662_);
lean_dec_ref(v_x_660_);
v_r_665_ = lean_box(v_res_664_);
return v_r_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2(lean_object* v_00_u03b2_666_, lean_object* v_x_667_, size_t v_x_668_, size_t v_x_669_, lean_object* v_x_670_, lean_object* v_x_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_x_667_, v_x_668_, v_x_669_, v_x_670_, v_x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___boxed(lean_object* v_00_u03b2_673_, lean_object* v_x_674_, lean_object* v_x_675_, lean_object* v_x_676_, lean_object* v_x_677_, lean_object* v_x_678_){
_start:
{
size_t v_x_763__boxed_679_; size_t v_x_764__boxed_680_; lean_object* v_res_681_; 
v_x_763__boxed_679_ = lean_unbox_usize(v_x_675_);
lean_dec(v_x_675_);
v_x_764__boxed_680_ = lean_unbox_usize(v_x_676_);
lean_dec(v_x_676_);
v_res_681_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2(v_00_u03b2_673_, v_x_674_, v_x_763__boxed_679_, v_x_764__boxed_680_, v_x_677_, v_x_678_);
return v_res_681_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_682_, lean_object* v_keys_683_, lean_object* v_vals_684_, lean_object* v_heq_685_, lean_object* v_i_686_, lean_object* v_k_687_){
_start:
{
uint8_t v___x_688_; 
v___x_688_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg(v_keys_683_, v_i_686_, v_k_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_689_, lean_object* v_keys_690_, lean_object* v_vals_691_, lean_object* v_heq_692_, lean_object* v_i_693_, lean_object* v_k_694_){
_start:
{
uint8_t v_res_695_; lean_object* v_r_696_; 
v_res_695_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1(v_00_u03b2_689_, v_keys_690_, v_vals_691_, v_heq_692_, v_i_693_, v_k_694_);
lean_dec(v_k_694_);
lean_dec_ref(v_vals_691_);
lean_dec_ref(v_keys_690_);
v_r_696_ = lean_box(v_res_695_);
return v_r_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_697_, lean_object* v_n_698_, lean_object* v_k_699_, lean_object* v_v_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4___redArg(v_n_698_, v_k_699_, v_v_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_702_, size_t v_depth_703_, lean_object* v_keys_704_, lean_object* v_vals_705_, lean_object* v_heq_706_, lean_object* v_i_707_, lean_object* v_entries_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg(v_depth_703_, v_keys_704_, v_vals_705_, v_i_707_, v_entries_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_710_, lean_object* v_depth_711_, lean_object* v_keys_712_, lean_object* v_vals_713_, lean_object* v_heq_714_, lean_object* v_i_715_, lean_object* v_entries_716_){
_start:
{
size_t v_depth_boxed_717_; lean_object* v_res_718_; 
v_depth_boxed_717_ = lean_unbox_usize(v_depth_711_);
lean_dec(v_depth_711_);
v_res_718_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5(v_00_u03b2_710_, v_depth_boxed_717_, v_keys_712_, v_vals_713_, v_heq_714_, v_i_715_, v_entries_716_);
lean_dec_ref(v_vals_713_);
lean_dec_ref(v_keys_712_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_719_, lean_object* v_x_720_, lean_object* v_x_721_, lean_object* v_x_722_, lean_object* v_x_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4_spec__5___redArg(v_x_720_, v_x_721_, v_x_722_, v_x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___lam__0(lean_object* v_count_725_, lean_object* v_x_726_, lean_object* v_x_727_){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_unsigned_to_nat(1u);
v___x_729_ = lean_nat_add(v_count_725_, v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___lam__0___boxed(lean_object* v_count_730_, lean_object* v_x_731_, lean_object* v_x_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___lam__0(v_count_730_, v_x_731_, v_x_732_);
lean_dec(v_x_732_);
lean_dec(v_x_731_);
lean_dec(v_count_730_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg(lean_object* v_state_738_){
_start:
{
lean_object* v___f_739_; lean_object* v___x_740_; lean_object* v_numEntries_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___f_739_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__0));
v___x_740_ = lean_unsigned_to_nat(0u);
v_numEntries_741_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_state_738_, v___f_739_, v___x_740_);
v___x_742_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__2));
v___x_743_ = l_Nat_reprFast(v_numEntries_741_);
v___x_744_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
v___x_745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_742_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___boxed(lean_object* v_state_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg(v_state_746_);
lean_dec_ref(v_state_746_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn(uint8_t v_pu_748_, lean_object* v_00_u03b2_749_, lean_object* v_state_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg(v_state_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___boxed(lean_object* v_pu_752_, lean_object* v_00_u03b2_753_, lean_object* v_state_754_){
_start:
{
uint8_t v_pu_boxed_755_; lean_object* v_res_756_; 
v_pu_boxed_755_ = lean_unbox(v_pu_752_);
v_res_756_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn(v_pu_boxed_755_, v_00_u03b2_753_, v_state_754_);
lean_dec_ref(v_state_754_);
return v_res_756_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___redArg(lean_object* v_a_757_, lean_object* v_b_758_){
_start:
{
lean_object* v_toSignature_759_; lean_object* v_toSignature_760_; lean_object* v_name_761_; lean_object* v_name_762_; uint8_t v___x_763_; 
v_toSignature_759_ = lean_ctor_get(v_a_757_, 0);
v_toSignature_760_ = lean_ctor_get(v_b_758_, 0);
v_name_761_ = lean_ctor_get(v_toSignature_759_, 0);
v_name_762_ = lean_ctor_get(v_toSignature_760_, 0);
v___x_763_ = l_Lean_Name_quickLt(v_name_761_, v_name_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___redArg___boxed(lean_object* v_a_764_, lean_object* v_b_765_){
_start:
{
uint8_t v_res_766_; lean_object* v_r_767_; 
v_res_766_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___redArg(v_a_764_, v_b_765_);
lean_dec_ref(v_b_765_);
lean_dec_ref(v_a_764_);
v_r_767_ = lean_box(v_res_766_);
return v_r_767_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt(uint8_t v_pu_768_, lean_object* v_a_769_, lean_object* v_b_770_){
_start:
{
lean_object* v_toSignature_771_; lean_object* v_toSignature_772_; lean_object* v_name_773_; lean_object* v_name_774_; uint8_t v___x_775_; 
v_toSignature_771_ = lean_ctor_get(v_a_769_, 0);
v_toSignature_772_ = lean_ctor_get(v_b_770_, 0);
v_name_773_ = lean_ctor_get(v_toSignature_771_, 0);
v_name_774_ = lean_ctor_get(v_toSignature_772_, 0);
v___x_775_ = l_Lean_Name_quickLt(v_name_773_, v_name_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___boxed(lean_object* v_pu_776_, lean_object* v_a_777_, lean_object* v_b_778_){
_start:
{
uint8_t v_pu_boxed_779_; uint8_t v_res_780_; lean_object* v_r_781_; 
v_pu_boxed_779_ = lean_unbox(v_pu_776_);
v_res_780_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt(v_pu_boxed_779_, v_a_777_, v_b_778_);
lean_dec_ref(v_b_778_);
lean_dec_ref(v_a_777_);
v_r_781_ = lean_box(v_res_780_);
return v_r_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f(uint8_t v_pu_783_, lean_object* v_decls_784_, lean_object* v_declName_785_){
_start:
{
lean_object* v_tmpDecl_786_; lean_object* v_toSignature_787_; lean_object* v_value_788_; uint8_t v_recursive_789_; lean_object* v_inlineAttr_x3f_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_821_; 
v_tmpDecl_786_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default(v_pu_783_);
v_toSignature_787_ = lean_ctor_get(v_tmpDecl_786_, 0);
v_value_788_ = lean_ctor_get(v_tmpDecl_786_, 1);
v_recursive_789_ = lean_ctor_get_uint8(v_tmpDecl_786_, sizeof(void*)*3);
v_inlineAttr_x3f_790_ = lean_ctor_get(v_tmpDecl_786_, 2);
v_isSharedCheck_821_ = !lean_is_exclusive(v_tmpDecl_786_);
if (v_isSharedCheck_821_ == 0)
{
v___x_792_ = v_tmpDecl_786_;
v_isShared_793_ = v_isSharedCheck_821_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_inlineAttr_x3f_790_);
lean_inc(v_value_788_);
lean_inc(v_toSignature_787_);
lean_dec(v_tmpDecl_786_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_821_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v_levelParams_794_; lean_object* v_type_795_; lean_object* v_params_796_; uint8_t v_safe_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_819_; 
v_levelParams_794_ = lean_ctor_get(v_toSignature_787_, 1);
v_type_795_ = lean_ctor_get(v_toSignature_787_, 2);
v_params_796_ = lean_ctor_get(v_toSignature_787_, 3);
v_safe_797_ = lean_ctor_get_uint8(v_toSignature_787_, sizeof(void*)*4);
v_isSharedCheck_819_ = !lean_is_exclusive(v_toSignature_787_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v_toSignature_787_, 0);
lean_dec(v_unused_820_);
v___x_799_ = v_toSignature_787_;
v_isShared_800_ = v_isSharedCheck_819_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_params_796_);
lean_inc(v_type_795_);
lean_inc(v_levelParams_794_);
lean_dec(v_toSignature_787_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_819_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_801_ = lean_unsigned_to_nat(0u);
v___x_802_ = lean_array_get_size(v_decls_784_);
v___x_803_ = lean_nat_dec_lt(v___x_801_, v___x_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; 
lean_del_object(v___x_799_);
lean_dec_ref(v_params_796_);
lean_dec_ref(v_type_795_);
lean_dec(v_levelParams_794_);
lean_del_object(v___x_792_);
lean_dec(v_inlineAttr_x3f_790_);
lean_dec_ref(v_value_788_);
lean_dec(v_declName_785_);
v___x_804_ = lean_box(0);
return v___x_804_;
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_805_ = lean_unsigned_to_nat(1u);
v___x_806_ = lean_nat_sub(v___x_802_, v___x_805_);
v___x_807_ = lean_nat_dec_le(v___x_801_, v___x_806_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; 
lean_dec(v___x_806_);
lean_del_object(v___x_799_);
lean_dec_ref(v_params_796_);
lean_dec_ref(v_type_795_);
lean_dec(v_levelParams_794_);
lean_del_object(v___x_792_);
lean_dec(v_inlineAttr_x3f_790_);
lean_dec_ref(v_value_788_);
lean_dec(v_declName_785_);
v___x_808_ = lean_box(0);
return v___x_808_;
}
else
{
lean_object* v___x_810_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v_declName_785_);
v___x_810_ = v___x_799_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_declName_785_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_levelParams_794_);
lean_ctor_set(v_reuseFailAlloc_818_, 2, v_type_795_);
lean_ctor_set(v_reuseFailAlloc_818_, 3, v_params_796_);
lean_ctor_set_uint8(v_reuseFailAlloc_818_, sizeof(void*)*4, v_safe_797_);
v___x_810_ = v_reuseFailAlloc_818_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v_tmpDecl_812_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_810_);
v_tmpDecl_812_ = v___x_792_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_value_788_);
lean_ctor_set(v_reuseFailAlloc_817_, 2, v_inlineAttr_x3f_790_);
lean_ctor_set_uint8(v_reuseFailAlloc_817_, sizeof(void*)*3, v_recursive_789_);
v_tmpDecl_812_ = v_reuseFailAlloc_817_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_813_ = lean_box(v_pu_783_);
v___x_814_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___boxed), 3, 1);
lean_closure_set(v___x_814_, 0, v___x_813_);
v___x_815_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0));
v___x_816_ = l_Array_binSearchAux___redArg(v___x_814_, v___x_815_, v_decls_784_, v_tmpDecl_812_, v___x_801_, v___x_806_);
return v___x_816_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___boxed(lean_object* v_pu_822_, lean_object* v_decls_823_, lean_object* v_declName_824_){
_start:
{
uint8_t v_pu_boxed_825_; lean_object* v_res_826_; 
v_pu_boxed_825_ = lean_unbox(v_pu_822_);
v_res_826_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f(v_pu_boxed_825_, v_decls_823_, v_declName_824_);
lean_dec_ref(v_decls_823_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0(lean_object* v_x_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__1));
v___x_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___boxed(lean_object* v_x_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0(v_x_835_, v___y_836_);
lean_dec_ref(v___y_836_);
lean_dec_ref(v_x_835_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__1(lean_object* v_s_839_, lean_object* v_x_840_){
_start:
{
lean_inc_ref(v_s_839_);
return v_s_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__1___boxed(lean_object* v_s_841_, lean_object* v_x_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__1(v_s_841_, v_x_842_);
lean_dec_ref(v_x_842_);
lean_dec_ref(v_s_841_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2(lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__1));
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___boxed(lean_object* v_x_851_, lean_object* v_x_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2(v_x_851_, v_x_852_);
lean_dec_ref(v_x_852_);
lean_dec_ref(v_x_851_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__3(lean_object* v_x_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = lean_box(0);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__3___boxed(lean_object* v_x_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__3(v_x_856_);
lean_dec_ref(v_x_856_);
return v_res_857_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__4(void){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_862_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5(void){
_start:
{
lean_object* v___f_863_; lean_object* v___f_864_; lean_object* v___f_865_; lean_object* v___f_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___f_863_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__3));
v___f_864_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__2));
v___f_865_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__1));
v___f_866_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__0));
v___x_867_ = lean_box(0);
v___x_868_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__4, &l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__4_once, _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__4);
v___x_869_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
lean_ctor_set(v___x_869_, 1, v___x_867_);
lean_ctor_set(v___x_869_, 2, v___f_866_);
lean_ctor_set(v___x_869_, 3, v___f_865_);
lean_ctor_set(v___x_869_, 4, v___f_864_);
lean_ctor_set(v___x_869_, 5, v___f_863_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1(uint8_t v_pu_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5, &l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5_once, _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___boxed(lean_object* v_pu_872_){
_start:
{
uint8_t v_pu_boxed_873_; lean_object* v_res_874_; 
v_pu_boxed_873_ = lean_unbox(v_pu_872_);
v_res_874_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1(v_pu_boxed_873_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt(uint8_t v_pu_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5, &l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5_once, _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___boxed(lean_object* v_pu_877_){
_start:
{
uint8_t v_pu_boxed_878_; lean_object* v_res_879_; 
v_pu_boxed_878_ = lean_unbox(v_pu_877_);
v_res_879_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt(v_pu_boxed_878_);
return v_res_879_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__10));
v___x_907_ = l_Lean_mkAtom(v___x_906_);
return v___x_907_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_908_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12);
v___x_909_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5));
v___x_910_ = lean_array_push(v___x_909_, v___x_908_);
return v___x_910_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__17));
v___x_920_ = l_Lean_mkAtom(v___x_919_);
return v___x_920_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_921_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18);
v___x_922_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5));
v___x_923_ = lean_array_push(v___x_922_, v___x_921_);
return v___x_923_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_924_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19);
v___x_925_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16));
v___x_926_ = lean_box(2);
v___x_927_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v___x_925_);
lean_ctor_set(v___x_927_, 2, v___x_924_);
return v___x_927_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_928_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20);
v___x_929_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13);
v___x_930_ = lean_array_push(v___x_929_, v___x_928_);
return v___x_930_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_931_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21);
v___x_932_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11));
v___x_933_ = lean_box(2);
v___x_934_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v___x_932_);
lean_ctor_set(v___x_934_, 2, v___x_931_);
return v___x_934_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_935_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22);
v___x_936_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5));
v___x_937_ = lean_array_push(v___x_936_, v___x_935_);
return v___x_937_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_938_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23);
v___x_939_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__9));
v___x_940_ = lean_box(2);
v___x_941_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set(v___x_941_, 1, v___x_939_);
lean_ctor_set(v___x_941_, 2, v___x_938_);
return v___x_941_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_942_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24);
v___x_943_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5));
v___x_944_ = lean_array_push(v___x_943_, v___x_942_);
return v___x_944_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_945_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25);
v___x_946_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7));
v___x_947_ = lean_box(2);
v___x_948_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
lean_ctor_set(v___x_948_, 1, v___x_946_);
lean_ctor_set(v___x_948_, 2, v___x_945_);
return v___x_948_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_949_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26);
v___x_950_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5));
v___x_951_ = lean_array_push(v___x_950_, v___x_949_);
return v___x_951_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_952_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27);
v___x_953_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4));
v___x_954_ = lean_box(2);
v___x_955_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v___x_953_);
lean_ctor_set(v___x_955_, 2, v___x_952_);
return v___x_955_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1(void){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__0(lean_object* v_s_957_, lean_object* v_decl_958_){
_start:
{
lean_object* v_toSignature_959_; lean_object* v_name_960_; lean_object* v___x_961_; 
v_toSignature_959_ = lean_ctor_get(v_decl_958_, 0);
v_name_960_ = lean_ctor_get(v_toSignature_959_, 0);
lean_inc(v_name_960_);
v___x_961_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_s_957_, v_name_960_, v_decl_958_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__1(lean_object* v_x_962_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__0));
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__1___boxed(lean_object* v_x_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__1(v_x_964_);
lean_dec_ref(v_x_964_);
return v_res_965_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_mkDeclExt___lam__2(lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_toSignature_968_; lean_object* v_toSignature_969_; lean_object* v_name_970_; lean_object* v_name_971_; uint8_t v___x_972_; 
v_toSignature_968_ = lean_ctor_get(v___y_966_, 0);
v_toSignature_969_ = lean_ctor_get(v___y_967_, 0);
v_name_970_ = lean_ctor_get(v_toSignature_968_, 0);
v_name_971_ = lean_ctor_get(v_toSignature_969_, 0);
v___x_972_ = l_Lean_Name_quickLt(v_name_970_, v_name_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__2___boxed(lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
uint8_t v_res_975_; lean_object* v_r_976_; 
v_res_975_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__2(v___y_973_, v___y_974_);
lean_dec_ref(v___y_974_);
lean_dec_ref(v___y_973_);
v_r_976_ = lean_box(v_res_975_);
return v_r_976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(lean_object* v_env_982_, uint8_t v_phase_983_, lean_object* v_as_984_, size_t v_i_985_, size_t v_stop_986_, lean_object* v_b_987_){
_start:
{
lean_object* v___y_989_; uint8_t v___x_993_; 
v___x_993_ = lean_usize_dec_eq(v_i_985_, v_stop_986_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; lean_object* v_toSignature_995_; uint8_t v_recursive_996_; lean_object* v_inlineAttr_x3f_997_; lean_object* v_name_998_; uint8_t v___x_999_; 
v___x_994_ = lean_array_uget(v_as_984_, v_i_985_);
v_toSignature_995_ = lean_ctor_get(v___x_994_, 0);
v_recursive_996_ = lean_ctor_get_uint8(v___x_994_, sizeof(void*)*3);
v_inlineAttr_x3f_997_ = lean_ctor_get(v___x_994_, 2);
v_name_998_ = lean_ctor_get(v_toSignature_995_, 0);
lean_inc_ref(v_env_982_);
v___x_999_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_982_, v_name_998_);
if (v___x_999_ == 0)
{
lean_dec(v___x_994_);
v___y_989_ = v_b_987_;
goto v___jp_988_;
}
else
{
uint8_t v___x_1000_; 
lean_inc_ref(v_env_982_);
v___x_1000_ = l_Lean_Compiler_LCNF_isDeclTransparent(v_env_982_, v_phase_983_, v_name_998_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1009_; 
lean_inc(v_inlineAttr_x3f_997_);
lean_inc_ref(v_toSignature_995_);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; lean_object* v_unused_1011_; lean_object* v_unused_1012_; 
v_unused_1010_ = lean_ctor_get(v___x_994_, 2);
lean_dec(v_unused_1010_);
v_unused_1011_ = lean_ctor_get(v___x_994_, 1);
lean_dec(v_unused_1011_);
v_unused_1012_ = lean_ctor_get(v___x_994_, 0);
lean_dec(v_unused_1012_);
v___x_1002_ = v___x_994_;
v_isShared_1003_ = v_isSharedCheck_1009_;
goto v_resetjp_1001_;
}
else
{
lean_dec(v___x_994_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1009_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1004_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__1));
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 1, v___x_1004_);
v___x_1006_ = v___x_1002_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_toSignature_995_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1008_, 2, v_inlineAttr_x3f_997_);
lean_ctor_set_uint8(v_reuseFailAlloc_1008_, sizeof(void*)*3, v_recursive_996_);
v___x_1006_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_array_push(v_b_987_, v___x_1006_);
v___y_989_ = v___x_1007_;
goto v___jp_988_;
}
}
}
else
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_array_push(v_b_987_, v___x_994_);
v___y_989_ = v___x_1013_;
goto v___jp_988_;
}
}
}
else
{
lean_dec_ref(v_env_982_);
return v_b_987_;
}
v___jp_988_:
{
size_t v___x_990_; size_t v___x_991_; 
v___x_990_ = ((size_t)1ULL);
v___x_991_ = lean_usize_add(v_i_985_, v___x_990_);
v_i_985_ = v___x_991_;
v_b_987_ = v___y_989_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___boxed(lean_object* v_env_1014_, lean_object* v_phase_1015_, lean_object* v_as_1016_, lean_object* v_i_1017_, lean_object* v_stop_1018_, lean_object* v_b_1019_){
_start:
{
uint8_t v_phase_boxed_1020_; size_t v_i_boxed_1021_; size_t v_stop_boxed_1022_; lean_object* v_res_1023_; 
v_phase_boxed_1020_ = lean_unbox(v_phase_1015_);
v_i_boxed_1021_ = lean_unbox_usize(v_i_1017_);
lean_dec(v_i_1017_);
v_stop_boxed_1022_ = lean_unbox_usize(v_stop_1018_);
lean_dec(v_stop_1018_);
v_res_1023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(v_env_1014_, v_phase_boxed_1020_, v_as_1016_, v_i_boxed_1021_, v_stop_boxed_1022_, v_b_1019_);
lean_dec_ref(v_as_1016_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0(lean_object* v_env_1024_, uint8_t v_phase_1025_, uint8_t v___x_1026_, lean_object* v_as_1027_, lean_object* v_start_1028_, lean_object* v_stop_1029_){
_start:
{
lean_object* v___x_1030_; uint8_t v___x_1031_; 
v___x_1030_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__0));
v___x_1031_ = lean_nat_dec_lt(v_start_1028_, v_stop_1029_);
if (v___x_1031_ == 0)
{
lean_dec_ref(v_env_1024_);
return v___x_1030_;
}
else
{
lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1032_ = lean_array_get_size(v_as_1027_);
v___x_1033_ = lean_nat_dec_le(v_stop_1029_, v___x_1032_);
if (v___x_1033_ == 0)
{
uint8_t v___x_1034_; 
v___x_1034_ = lean_nat_dec_lt(v_start_1028_, v___x_1032_);
if (v___x_1034_ == 0)
{
lean_dec_ref(v_env_1024_);
return v___x_1030_;
}
else
{
size_t v___x_1035_; size_t v___x_1036_; lean_object* v___x_1037_; 
v___x_1035_ = lean_usize_of_nat(v_start_1028_);
v___x_1036_ = lean_usize_of_nat(v___x_1032_);
v___x_1037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(v_env_1024_, v_phase_1025_, v_as_1027_, v___x_1035_, v___x_1036_, v___x_1030_);
return v___x_1037_;
}
}
else
{
size_t v___x_1038_; size_t v___x_1039_; lean_object* v___x_1040_; 
v___x_1038_ = lean_usize_of_nat(v_start_1028_);
v___x_1039_ = lean_usize_of_nat(v_stop_1029_);
v___x_1040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(v_env_1024_, v_phase_1025_, v_as_1027_, v___x_1038_, v___x_1039_, v___x_1030_);
return v___x_1040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0___boxed(lean_object* v_env_1041_, lean_object* v_phase_1042_, lean_object* v___x_1043_, lean_object* v_as_1044_, lean_object* v_start_1045_, lean_object* v_stop_1046_){
_start:
{
uint8_t v_phase_boxed_1047_; uint8_t v___x_1056__boxed_1048_; lean_object* v_res_1049_; 
v_phase_boxed_1047_ = lean_unbox(v_phase_1042_);
v___x_1056__boxed_1048_ = lean_unbox(v___x_1043_);
v_res_1049_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0(v_env_1041_, v_phase_boxed_1047_, v___x_1056__boxed_1048_, v_as_1044_, v_start_1045_, v_stop_1046_);
lean_dec(v_stop_1046_);
lean_dec(v_start_1045_);
lean_dec_ref(v_as_1044_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__3(uint8_t v_phase_1050_, lean_object* v___f_1051_, lean_object* v_env_1052_, lean_object* v_s_1053_){
_start:
{
uint8_t v___x_1054_; lean_object* v_all_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v_exported_1058_; lean_object* v___x_1059_; 
v___x_1054_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_1050_);
v_all_1055_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(v_s_1053_, v___f_1051_);
v___x_1056_ = lean_unsigned_to_nat(0u);
v___x_1057_ = lean_array_get_size(v_all_1055_);
v_exported_1058_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0(v_env_1052_, v_phase_1050_, v___x_1054_, v_all_1055_, v___x_1056_, v___x_1057_);
lean_inc_ref(v_exported_1058_);
v___x_1059_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1059_, 0, v_exported_1058_);
lean_ctor_set(v___x_1059_, 1, v_exported_1058_);
lean_ctor_set(v___x_1059_, 2, v_all_1055_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__3___boxed(lean_object* v_phase_1060_, lean_object* v___f_1061_, lean_object* v_env_1062_, lean_object* v_s_1063_){
_start:
{
uint8_t v_phase_boxed_1064_; lean_object* v_res_1065_; 
v_phase_boxed_1064_ = lean_unbox(v_phase_1060_);
v_res_1065_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__3(v_phase_boxed_1064_, v___f_1061_, v_env_1062_, v_s_1063_);
lean_dec_ref(v_s_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__4(lean_object* v___x_1066_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__4___boxed(lean_object* v___x_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__4(v___x_1069_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__5(lean_object* v___x_1072_, lean_object* v_x_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1072_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__5___boxed(lean_object* v___x_1077_, lean_object* v_x_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__5(v___x_1077_, v_x_1078_, v___y_1079_);
lean_dec_ref(v___y_1079_);
lean_dec_ref(v_x_1078_);
return v_res_1081_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__3(void){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1085_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__4(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__3, &l_Lean_Compiler_LCNF_mkDeclExt___closed__3_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__3);
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
return v___x_1087_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__5(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___f_1089_; 
v___x_1088_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__4, &l_Lean_Compiler_LCNF_mkDeclExt___closed__4_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__4);
v___f_1089_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkDeclExt___lam__4___boxed), 2, 1);
lean_closure_set(v___f_1089_, 0, v___x_1088_);
return v___f_1089_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__6(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___f_1091_; 
v___x_1090_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__4, &l_Lean_Compiler_LCNF_mkDeclExt___closed__4_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__4);
v___f_1091_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkDeclExt___lam__5___boxed), 4, 1);
lean_closure_set(v___f_1091_, 0, v___x_1090_);
return v___f_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt(uint8_t v_phase_1092_, lean_object* v_name_1093_){
_start:
{
lean_object* v___f_1095_; lean_object* v___f_1096_; lean_object* v___f_1097_; lean_object* v___x_1098_; lean_object* v___f_1099_; lean_object* v___f_1100_; lean_object* v___f_1101_; uint8_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___f_1095_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___closed__0));
v___f_1096_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___closed__1));
v___f_1097_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___closed__2));
v___x_1098_ = lean_box(v_phase_1092_);
v___f_1099_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkDeclExt___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1099_, 0, v___x_1098_);
lean_closure_set(v___f_1099_, 1, v___f_1097_);
v___f_1100_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__5, &l_Lean_Compiler_LCNF_mkDeclExt___closed__5_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__5);
v___f_1101_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__6, &l_Lean_Compiler_LCNF_mkDeclExt___closed__6_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__6);
v___x_1102_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_1092_);
v___x_1103_ = lean_box(v___x_1102_);
v___x_1104_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___boxed), 3, 2);
lean_closure_set(v___x_1104_, 0, v___x_1103_);
lean_closure_set(v___x_1104_, 1, lean_box(0));
v___x_1105_ = lean_box(0);
v___x_1106_ = lean_box(v_phase_1092_);
v___x_1107_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___boxed), 6, 2);
lean_closure_set(v___x_1107_, 0, lean_box(0));
lean_closure_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
v___x_1109_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1109_, 0, v_name_1093_);
lean_ctor_set(v___x_1109_, 1, v___f_1100_);
lean_ctor_set(v___x_1109_, 2, v___f_1101_);
lean_ctor_set(v___x_1109_, 3, v___f_1095_);
lean_ctor_set(v___x_1109_, 4, v___f_1099_);
lean_ctor_set(v___x_1109_, 5, v___x_1104_);
lean_ctor_set(v___x_1109_, 6, v___x_1105_);
lean_ctor_set(v___x_1109_, 7, v___x_1108_);
v___x_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
lean_ctor_set(v___x_1110_, 1, v___f_1096_);
v___x_1111_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___boxed(lean_object* v_phase_1112_, lean_object* v_name_1113_, lean_object* v_a_1114_){
_start:
{
uint8_t v_phase_boxed_1115_; lean_object* v_res_1116_; 
v_phase_boxed_1115_ = lean_unbox(v_phase_1112_);
v_res_1116_ = l_Lean_Compiler_LCNF_mkDeclExt(v_phase_boxed_1115_, v_name_1113_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0(lean_object* v_env_1117_, uint8_t v_phase_1118_, uint8_t v___x_1119_, lean_object* v_as_1120_, size_t v_i_1121_, size_t v_stop_1122_, lean_object* v_b_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(v_env_1117_, v_phase_1118_, v_as_1120_, v_i_1121_, v_stop_1122_, v_b_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___boxed(lean_object* v_env_1125_, lean_object* v_phase_1126_, lean_object* v___x_1127_, lean_object* v_as_1128_, lean_object* v_i_1129_, lean_object* v_stop_1130_, lean_object* v_b_1131_){
_start:
{
uint8_t v_phase_boxed_1132_; uint8_t v___x_1182__boxed_1133_; size_t v_i_boxed_1134_; size_t v_stop_boxed_1135_; lean_object* v_res_1136_; 
v_phase_boxed_1132_ = lean_unbox(v_phase_1126_);
v___x_1182__boxed_1133_ = lean_unbox(v___x_1127_);
v_i_boxed_1134_ = lean_unbox_usize(v_i_1129_);
lean_dec(v_i_1129_);
v_stop_boxed_1135_ = lean_unbox_usize(v_stop_1130_);
lean_dec(v_stop_1130_);
v_res_1136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0(v_env_1125_, v_phase_boxed_1132_, v___x_1182__boxed_1133_, v_as_1128_, v_i_boxed_1134_, v_stop_boxed_1135_, v_b_1131_);
lean_dec_ref(v_as_1128_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1146_ = 0;
v___x_1147_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_));
v___x_1148_ = l_Lean_Compiler_LCNF_mkDeclExt(v___x_1146_, v___x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2____boxed(lean_object* v_a_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_();
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1158_ = 1;
v___x_1159_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_));
v___x_1160_ = l_Lean_Compiler_LCNF_mkDeclExt(v___x_1158_, v___x_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2____boxed(lean_object* v_a_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_();
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___f_1169_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__5, &l_Lean_Compiler_LCNF_mkDeclExt___closed__5_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__5);
v___x_1170_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_));
v___x_1171_ = lean_box(0);
v___x_1172_ = l_Lean_registerEnvExtension___redArg(v___f_1169_, v___x_1170_, v___x_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2____boxed(lean_object* v_a_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_();
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__0(lean_object* v_x_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__1));
v___x_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__0___boxed(lean_object* v_x_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__0(v_x_1180_, v___y_1181_);
lean_dec_ref(v___y_1181_);
lean_dec_ref(v_x_1180_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__1(lean_object* v_s_1184_, lean_object* v_x_1185_){
_start:
{
lean_inc_ref(v_s_1184_);
return v_s_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__1___boxed(lean_object* v_s_1186_, lean_object* v_x_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__1(v_s_1186_, v_x_1187_);
lean_dec_ref(v_x_1187_);
lean_dec_ref(v_s_1186_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2(lean_object* v_x_1193_, lean_object* v_x_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__1));
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___boxed(lean_object* v_x_1196_, lean_object* v_x_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2(v_x_1196_, v_x_1197_);
lean_dec_ref(v_x_1197_);
lean_dec_ref(v_x_1196_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__3(lean_object* v_x_1199_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = lean_box(0);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__3___boxed(lean_object* v_x_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__3(v_x_1201_);
lean_dec_ref(v_x_1201_);
return v_res_1202_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__4(void){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1207_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5(void){
_start:
{
lean_object* v___f_1208_; lean_object* v___f_1209_; lean_object* v___f_1210_; lean_object* v___f_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___f_1208_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__3));
v___f_1209_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__2));
v___f_1210_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__1));
v___f_1211_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__0));
v___x_1212_ = lean_box(0);
v___x_1213_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__4, &l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__4_once, _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__4);
v___x_1214_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
lean_ctor_set(v___x_1214_, 1, v___x_1212_);
lean_ctor_set(v___x_1214_, 2, v___f_1211_);
lean_ctor_set(v___x_1214_, 3, v___f_1210_);
lean_ctor_set(v___x_1214_, 4, v___f_1209_);
lean_ctor_set(v___x_1214_, 5, v___f_1208_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1(uint8_t v_pu_1215_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5, &l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5_once, _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___boxed(lean_object* v_pu_1217_){
_start:
{
uint8_t v_pu_boxed_1218_; lean_object* v_res_1219_; 
v_pu_boxed_1218_ = lean_unbox(v_pu_1217_);
v_res_1219_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1(v_pu_boxed_1218_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt(uint8_t v_pu_1220_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5, &l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5_once, _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___boxed(lean_object* v_pu_1222_){
_start:
{
uint8_t v_pu_boxed_1223_; lean_object* v_res_1224_; 
v_pu_boxed_1223_ = lean_unbox(v_pu_1222_);
v_res_1224_ = l_Lean_Compiler_LCNF_instInhabitedSigExt(v_pu_boxed_1223_);
return v_res_1224_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___redArg(lean_object* v_a_1225_, lean_object* v_b_1226_){
_start:
{
lean_object* v_name_1227_; lean_object* v_name_1228_; uint8_t v___x_1229_; 
v_name_1227_ = lean_ctor_get(v_a_1225_, 0);
v_name_1228_ = lean_ctor_get(v_b_1226_, 0);
v___x_1229_ = l_Lean_Name_quickLt(v_name_1227_, v_name_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___redArg___boxed(lean_object* v_a_1230_, lean_object* v_b_1231_){
_start:
{
uint8_t v_res_1232_; lean_object* v_r_1233_; 
v_res_1232_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___redArg(v_a_1230_, v_b_1231_);
lean_dec_ref(v_b_1231_);
lean_dec_ref(v_a_1230_);
v_r_1233_ = lean_box(v_res_1232_);
return v_r_1233_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt(uint8_t v_pu_1234_, lean_object* v_a_1235_, lean_object* v_b_1236_){
_start:
{
lean_object* v_name_1237_; lean_object* v_name_1238_; uint8_t v___x_1239_; 
v_name_1237_ = lean_ctor_get(v_a_1235_, 0);
v_name_1238_ = lean_ctor_get(v_b_1236_, 0);
v___x_1239_ = l_Lean_Name_quickLt(v_name_1237_, v_name_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___boxed(lean_object* v_pu_1240_, lean_object* v_a_1241_, lean_object* v_b_1242_){
_start:
{
uint8_t v_pu_boxed_1243_; uint8_t v_res_1244_; lean_object* v_r_1245_; 
v_pu_boxed_1243_ = lean_unbox(v_pu_1240_);
v_res_1244_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt(v_pu_boxed_1243_, v_a_1241_, v_b_1242_);
lean_dec_ref(v_b_1242_);
lean_dec_ref(v_a_1241_);
v_r_1245_ = lean_box(v_res_1244_);
return v_r_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f(uint8_t v_pu_1247_, lean_object* v_sigs_1248_, lean_object* v_declName_1249_){
_start:
{
lean_object* v_tmpSig_1250_; lean_object* v_levelParams_1251_; lean_object* v_type_1252_; lean_object* v_params_1253_; uint8_t v_safe_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1273_; 
v_tmpSig_1250_ = l_Lean_Compiler_LCNF_instInhabitedSignature_default(v_pu_1247_);
v_levelParams_1251_ = lean_ctor_get(v_tmpSig_1250_, 1);
v_type_1252_ = lean_ctor_get(v_tmpSig_1250_, 2);
v_params_1253_ = lean_ctor_get(v_tmpSig_1250_, 3);
v_safe_1254_ = lean_ctor_get_uint8(v_tmpSig_1250_, sizeof(void*)*4);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_tmpSig_1250_);
if (v_isSharedCheck_1273_ == 0)
{
lean_object* v_unused_1274_; 
v_unused_1274_ = lean_ctor_get(v_tmpSig_1250_, 0);
lean_dec(v_unused_1274_);
v___x_1256_ = v_tmpSig_1250_;
v_isShared_1257_ = v_isSharedCheck_1273_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_params_1253_);
lean_inc(v_type_1252_);
lean_inc(v_levelParams_1251_);
lean_dec(v_tmpSig_1250_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1273_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v___x_1258_ = lean_unsigned_to_nat(0u);
v___x_1259_ = lean_array_get_size(v_sigs_1248_);
v___x_1260_ = lean_nat_dec_lt(v___x_1258_, v___x_1259_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; 
lean_del_object(v___x_1256_);
lean_dec_ref(v_params_1253_);
lean_dec_ref(v_type_1252_);
lean_dec(v_levelParams_1251_);
lean_dec(v_declName_1249_);
v___x_1261_ = lean_box(0);
return v___x_1261_;
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1262_ = lean_unsigned_to_nat(1u);
v___x_1263_ = lean_nat_sub(v___x_1259_, v___x_1262_);
v___x_1264_ = lean_nat_dec_le(v___x_1258_, v___x_1263_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; 
lean_dec(v___x_1263_);
lean_del_object(v___x_1256_);
lean_dec_ref(v_params_1253_);
lean_dec_ref(v_type_1252_);
lean_dec(v_levelParams_1251_);
lean_dec(v_declName_1249_);
v___x_1265_ = lean_box(0);
return v___x_1265_;
}
else
{
lean_object* v_tmpSig_1267_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v_declName_1249_);
v_tmpSig_1267_ = v___x_1256_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_declName_1249_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_levelParams_1251_);
lean_ctor_set(v_reuseFailAlloc_1272_, 2, v_type_1252_);
lean_ctor_set(v_reuseFailAlloc_1272_, 3, v_params_1253_);
lean_ctor_set_uint8(v_reuseFailAlloc_1272_, sizeof(void*)*4, v_safe_1254_);
v_tmpSig_1267_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1268_ = lean_box(v_pu_1247_);
v___x_1269_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___boxed), 3, 1);
lean_closure_set(v___x_1269_, 0, v___x_1268_);
v___x_1270_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0));
v___x_1271_ = l_Array_binSearchAux___redArg(v___x_1269_, v___x_1270_, v_sigs_1248_, v_tmpSig_1267_, v___x_1258_, v___x_1263_);
return v___x_1271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___boxed(lean_object* v_pu_1275_, lean_object* v_sigs_1276_, lean_object* v_declName_1277_){
_start:
{
uint8_t v_pu_boxed_1278_; lean_object* v_res_1279_; 
v_pu_boxed_1278_ = lean_unbox(v_pu_1275_);
v_res_1279_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f(v_pu_boxed_1278_, v_sigs_1276_, v_declName_1277_);
lean_dec_ref(v_sigs_1276_);
return v_res_1279_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkSigDeclExt___auto__1(void){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__0(lean_object* v_s_1281_, lean_object* v_sig_1282_){
_start:
{
lean_object* v_name_1283_; lean_object* v___x_1284_; 
v_name_1283_ = lean_ctor_get(v_sig_1282_, 0);
lean_inc(v_name_1283_);
v___x_1284_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_s_1281_, v_name_1283_, v_sig_1282_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1(lean_object* v_x_1285_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__0));
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1___boxed(lean_object* v_x_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1(v_x_1287_);
lean_dec_ref(v_x_1287_);
return v_res_1288_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2(lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v_name_1291_; lean_object* v_name_1292_; uint8_t v___x_1293_; 
v_name_1291_ = lean_ctor_get(v___y_1289_, 0);
v_name_1292_ = lean_ctor_get(v___y_1290_, 0);
v___x_1293_ = l_Lean_Name_quickLt(v_name_1291_, v_name_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2___boxed(lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
uint8_t v_res_1296_; lean_object* v_r_1297_; 
v_res_1296_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2(v___y_1294_, v___y_1295_);
lean_dec_ref(v___y_1295_);
lean_dec_ref(v___y_1294_);
v_r_1297_ = lean_box(v_res_1296_);
return v_r_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0(lean_object* v_env_1298_, lean_object* v_as_1299_, size_t v_i_1300_, size_t v_stop_1301_, lean_object* v_b_1302_){
_start:
{
lean_object* v___y_1304_; uint8_t v___x_1308_; 
v___x_1308_ = lean_usize_dec_eq(v_i_1300_, v_stop_1301_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v_name_1310_; uint8_t v___x_1311_; 
v___x_1309_ = lean_array_uget_borrowed(v_as_1299_, v_i_1300_);
v_name_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc_ref(v_env_1298_);
v___x_1311_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_1298_, v_name_1310_);
if (v___x_1311_ == 0)
{
v___y_1304_ = v_b_1302_;
goto v___jp_1303_;
}
else
{
lean_object* v___x_1312_; 
lean_inc(v___x_1309_);
v___x_1312_ = lean_array_push(v_b_1302_, v___x_1309_);
v___y_1304_ = v___x_1312_;
goto v___jp_1303_;
}
}
else
{
lean_dec_ref(v_env_1298_);
return v_b_1302_;
}
v___jp_1303_:
{
size_t v___x_1305_; size_t v___x_1306_; 
v___x_1305_ = ((size_t)1ULL);
v___x_1306_ = lean_usize_add(v_i_1300_, v___x_1305_);
v_i_1300_ = v___x_1306_;
v_b_1302_ = v___y_1304_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0___boxed(lean_object* v_env_1313_, lean_object* v_as_1314_, lean_object* v_i_1315_, lean_object* v_stop_1316_, lean_object* v_b_1317_){
_start:
{
size_t v_i_boxed_1318_; size_t v_stop_boxed_1319_; lean_object* v_res_1320_; 
v_i_boxed_1318_ = lean_unbox_usize(v_i_1315_);
lean_dec(v_i_1315_);
v_stop_boxed_1319_ = lean_unbox_usize(v_stop_1316_);
lean_dec(v_stop_1316_);
v_res_1320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0(v_env_1313_, v_as_1314_, v_i_boxed_1318_, v_stop_boxed_1319_, v_b_1317_);
lean_dec_ref(v_as_1314_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0(lean_object* v_env_1321_, lean_object* v_as_1322_, lean_object* v_start_1323_, lean_object* v_stop_1324_){
_start:
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__0));
v___x_1326_ = lean_nat_dec_lt(v_start_1323_, v_stop_1324_);
if (v___x_1326_ == 0)
{
lean_dec_ref(v_env_1321_);
return v___x_1325_;
}
else
{
lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1327_ = lean_array_get_size(v_as_1322_);
v___x_1328_ = lean_nat_dec_le(v_stop_1324_, v___x_1327_);
if (v___x_1328_ == 0)
{
uint8_t v___x_1329_; 
v___x_1329_ = lean_nat_dec_lt(v_start_1323_, v___x_1327_);
if (v___x_1329_ == 0)
{
lean_dec_ref(v_env_1321_);
return v___x_1325_;
}
else
{
size_t v___x_1330_; size_t v___x_1331_; lean_object* v___x_1332_; 
v___x_1330_ = lean_usize_of_nat(v_start_1323_);
v___x_1331_ = lean_usize_of_nat(v___x_1327_);
v___x_1332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0(v_env_1321_, v_as_1322_, v___x_1330_, v___x_1331_, v___x_1325_);
return v___x_1332_;
}
}
else
{
size_t v___x_1333_; size_t v___x_1334_; lean_object* v___x_1335_; 
v___x_1333_ = lean_usize_of_nat(v_start_1323_);
v___x_1334_ = lean_usize_of_nat(v_stop_1324_);
v___x_1335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0(v_env_1321_, v_as_1322_, v___x_1333_, v___x_1334_, v___x_1325_);
return v___x_1335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0___boxed(lean_object* v_env_1336_, lean_object* v_as_1337_, lean_object* v_start_1338_, lean_object* v_stop_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0(v_env_1336_, v_as_1337_, v_start_1338_, v_stop_1339_);
lean_dec(v_stop_1339_);
lean_dec(v_start_1338_);
lean_dec_ref(v_as_1337_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3(lean_object* v___f_1341_, lean_object* v_env_1342_, lean_object* v_s_1343_){
_start:
{
lean_object* v_all_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v_exported_1347_; lean_object* v___x_1348_; 
v_all_1344_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(v_s_1343_, v___f_1341_);
v___x_1345_ = lean_unsigned_to_nat(0u);
v___x_1346_ = lean_array_get_size(v_all_1344_);
v_exported_1347_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0(v_env_1342_, v_all_1344_, v___x_1345_, v___x_1346_);
lean_inc_ref(v_exported_1347_);
v___x_1348_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1348_, 0, v_exported_1347_);
lean_ctor_set(v___x_1348_, 1, v_exported_1347_);
lean_ctor_set(v___x_1348_, 2, v_all_1344_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3___boxed(lean_object* v___f_1349_, lean_object* v_env_1350_, lean_object* v_s_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3(v___f_1349_, v_env_1350_, v_s_1351_);
lean_dec_ref(v_s_1351_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__4(lean_object* v___x_1353_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1353_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__4___boxed(lean_object* v___x_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__4(v___x_1356_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__5(lean_object* v___x_1359_, lean_object* v_x_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1359_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__5___boxed(lean_object* v___x_1364_, lean_object* v_x_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__5(v___x_1364_, v_x_1365_, v___y_1366_);
lean_dec_ref(v___y_1366_);
lean_dec_ref(v_x_1365_);
return v_res_1368_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4(void){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1374_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5(void){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4, &l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4_once, _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4);
v___x_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
return v___x_1376_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6(void){
_start:
{
lean_object* v___x_1377_; lean_object* v___f_1378_; 
v___x_1377_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5, &l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5_once, _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5);
v___f_1378_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkSigDeclExt___lam__4___boxed), 2, 1);
lean_closure_set(v___f_1378_, 0, v___x_1377_);
return v___f_1378_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__7(void){
_start:
{
lean_object* v___x_1379_; lean_object* v___f_1380_; 
v___x_1379_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5, &l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5_once, _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5);
v___f_1380_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkSigDeclExt___lam__5___boxed), 4, 1);
lean_closure_set(v___f_1380_, 0, v___x_1379_);
return v___f_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt(uint8_t v_phase_1381_, lean_object* v_name_1382_){
_start:
{
lean_object* v___f_1384_; lean_object* v___f_1385_; lean_object* v___f_1386_; lean_object* v___f_1387_; lean_object* v___f_1388_; uint8_t v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___f_1384_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__0));
v___f_1385_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__1));
v___f_1386_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__3));
v___f_1387_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6, &l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6_once, _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6);
v___f_1388_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__7, &l_Lean_Compiler_LCNF_mkSigDeclExt___closed__7_once, _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__7);
v___x_1389_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_1381_);
v___x_1390_ = lean_box(v___x_1389_);
v___x_1391_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___boxed), 3, 2);
lean_closure_set(v___x_1391_, 0, v___x_1390_);
lean_closure_set(v___x_1391_, 1, lean_box(0));
v___x_1392_ = lean_box(0);
v___x_1393_ = lean_box(v_phase_1381_);
v___x_1394_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___boxed), 6, 2);
lean_closure_set(v___x_1394_, 0, lean_box(0));
lean_closure_set(v___x_1394_, 1, v___x_1393_);
v___x_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
v___x_1396_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1396_, 0, v_name_1382_);
lean_ctor_set(v___x_1396_, 1, v___f_1387_);
lean_ctor_set(v___x_1396_, 2, v___f_1388_);
lean_ctor_set(v___x_1396_, 3, v___f_1384_);
lean_ctor_set(v___x_1396_, 4, v___f_1386_);
lean_ctor_set(v___x_1396_, 5, v___x_1391_);
lean_ctor_set(v___x_1396_, 6, v___x_1392_);
lean_ctor_set(v___x_1396_, 7, v___x_1395_);
v___x_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
lean_ctor_set(v___x_1397_, 1, v___f_1385_);
v___x_1398_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___boxed(lean_object* v_phase_1399_, lean_object* v_name_1400_, lean_object* v_a_1401_){
_start:
{
uint8_t v_phase_boxed_1402_; lean_object* v_res_1403_; 
v_phase_boxed_1402_ = lean_unbox(v_phase_1399_);
v_res_1403_ = l_Lean_Compiler_LCNF_mkSigDeclExt(v_phase_boxed_1402_, v_name_1400_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1411_ = 2;
v___x_1412_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_));
v___x_1413_ = l_Lean_Compiler_LCNF_mkSigDeclExt(v___x_1411_, v___x_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2____boxed(lean_object* v_a_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_();
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(lean_object* v_as_1416_, lean_object* v_k_1417_, lean_object* v_x_1418_, lean_object* v_x_1419_){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v_m_1422_; lean_object* v_a_1423_; uint8_t v___x_1424_; 
v___x_1420_ = lean_nat_add(v_x_1418_, v_x_1419_);
v___x_1421_ = lean_unsigned_to_nat(1u);
v_m_1422_ = lean_nat_shiftr(v___x_1420_, v___x_1421_);
lean_dec(v___x_1420_);
v_a_1423_ = lean_array_fget_borrowed(v_as_1416_, v_m_1422_);
v___x_1424_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__2(v_a_1423_, v_k_1417_);
if (v___x_1424_ == 0)
{
uint8_t v___x_1425_; 
lean_dec(v_x_1419_);
v___x_1425_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__2(v_k_1417_, v_a_1423_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; 
lean_dec(v_m_1422_);
lean_dec(v_x_1418_);
lean_inc(v_a_1423_);
v___x_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1426_, 0, v_a_1423_);
return v___x_1426_;
}
else
{
lean_object* v___x_1427_; uint8_t v___x_1428_; 
v___x_1427_ = lean_unsigned_to_nat(0u);
v___x_1428_ = lean_nat_dec_eq(v_m_1422_, v___x_1427_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1429_ = lean_nat_sub(v_m_1422_, v___x_1421_);
lean_dec(v_m_1422_);
v___x_1430_ = lean_nat_dec_lt(v___x_1429_, v_x_1418_);
if (v___x_1430_ == 0)
{
v_x_1419_ = v___x_1429_;
goto _start;
}
else
{
lean_object* v___x_1432_; 
lean_dec(v___x_1429_);
lean_dec(v_x_1418_);
v___x_1432_ = lean_box(0);
return v___x_1432_;
}
}
else
{
lean_object* v___x_1433_; 
lean_dec(v_m_1422_);
lean_dec(v_x_1418_);
v___x_1433_ = lean_box(0);
return v___x_1433_;
}
}
}
else
{
lean_object* v___x_1434_; uint8_t v___x_1435_; 
lean_dec(v_x_1418_);
v___x_1434_ = lean_nat_add(v_m_1422_, v___x_1421_);
lean_dec(v_m_1422_);
v___x_1435_ = lean_nat_dec_le(v___x_1434_, v_x_1419_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; 
lean_dec(v___x_1434_);
lean_dec(v_x_1419_);
v___x_1436_ = lean_box(0);
return v___x_1436_;
}
else
{
v_x_1418_ = v___x_1434_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg___boxed(lean_object* v_as_1438_, lean_object* v_k_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(v_as_1438_, v_k_1439_, v_x_1440_, v_x_1441_);
lean_dec_ref(v_k_1439_);
lean_dec_ref(v_as_1438_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1443_, lean_object* v_vals_1444_, lean_object* v_i_1445_, lean_object* v_k_1446_){
_start:
{
lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1447_ = lean_array_get_size(v_keys_1443_);
v___x_1448_ = lean_nat_dec_lt(v_i_1445_, v___x_1447_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; 
lean_dec(v_i_1445_);
v___x_1449_ = lean_box(0);
return v___x_1449_;
}
else
{
lean_object* v_k_x27_1450_; uint8_t v___x_1451_; 
v_k_x27_1450_ = lean_array_fget_borrowed(v_keys_1443_, v_i_1445_);
v___x_1451_ = lean_name_eq(v_k_1446_, v_k_x27_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_unsigned_to_nat(1u);
v___x_1453_ = lean_nat_add(v_i_1445_, v___x_1452_);
lean_dec(v_i_1445_);
v_i_1445_ = v___x_1453_;
goto _start;
}
else
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_array_fget_borrowed(v_vals_1444_, v_i_1445_);
lean_dec(v_i_1445_);
lean_inc(v___x_1455_);
v___x_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
return v___x_1456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1457_, lean_object* v_vals_1458_, lean_object* v_i_1459_, lean_object* v_k_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1457_, v_vals_1458_, v_i_1459_, v_k_1460_);
lean_dec(v_k_1460_);
lean_dec_ref(v_vals_1458_);
lean_dec_ref(v_keys_1457_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg(lean_object* v_x_1462_, size_t v_x_1463_, lean_object* v_x_1464_){
_start:
{
if (lean_obj_tag(v_x_1462_) == 0)
{
lean_object* v_es_1465_; lean_object* v___x_1466_; size_t v___x_1467_; size_t v___x_1468_; lean_object* v_j_1469_; lean_object* v___x_1470_; 
v_es_1465_ = lean_ctor_get(v_x_1462_, 0);
v___x_1466_ = lean_box(2);
v___x_1467_ = ((size_t)31ULL);
v___x_1468_ = lean_usize_land(v_x_1463_, v___x_1467_);
v_j_1469_ = lean_usize_to_nat(v___x_1468_);
v___x_1470_ = lean_array_get_borrowed(v___x_1466_, v_es_1465_, v_j_1469_);
lean_dec(v_j_1469_);
switch(lean_obj_tag(v___x_1470_))
{
case 0:
{
lean_object* v_key_1471_; lean_object* v_val_1472_; uint8_t v___x_1473_; 
v_key_1471_ = lean_ctor_get(v___x_1470_, 0);
v_val_1472_ = lean_ctor_get(v___x_1470_, 1);
v___x_1473_ = lean_name_eq(v_x_1464_, v_key_1471_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; 
v___x_1474_ = lean_box(0);
return v___x_1474_;
}
else
{
lean_object* v___x_1475_; 
lean_inc(v_val_1472_);
v___x_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1475_, 0, v_val_1472_);
return v___x_1475_;
}
}
case 1:
{
lean_object* v_node_1476_; size_t v___x_1477_; size_t v___x_1478_; 
v_node_1476_ = lean_ctor_get(v___x_1470_, 0);
v___x_1477_ = ((size_t)5ULL);
v___x_1478_ = lean_usize_shift_right(v_x_1463_, v___x_1477_);
v_x_1462_ = v_node_1476_;
v_x_1463_ = v___x_1478_;
goto _start;
}
default: 
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_box(0);
return v___x_1480_;
}
}
}
else
{
lean_object* v_ks_1481_; lean_object* v_vs_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v_ks_1481_ = lean_ctor_get(v_x_1462_, 0);
v_vs_1482_ = lean_ctor_get(v_x_1462_, 1);
v___x_1483_ = lean_unsigned_to_nat(0u);
v___x_1484_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1481_, v_vs_1482_, v___x_1483_, v_x_1464_);
return v___x_1484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1485_, lean_object* v_x_1486_, lean_object* v_x_1487_){
_start:
{
size_t v_x_418__boxed_1488_; lean_object* v_res_1489_; 
v_x_418__boxed_1488_ = lean_unbox_usize(v_x_1486_);
lean_dec(v_x_1486_);
v_res_1489_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg(v_x_1485_, v_x_418__boxed_1488_, v_x_1487_);
lean_dec(v_x_1487_);
lean_dec_ref(v_x_1485_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(lean_object* v_x_1490_, lean_object* v_x_1491_){
_start:
{
uint64_t v___y_1493_; 
if (lean_obj_tag(v_x_1491_) == 0)
{
uint64_t v___x_1496_; 
v___x_1496_ = 1723ULL;
v___y_1493_ = v___x_1496_;
goto v___jp_1492_;
}
else
{
uint64_t v_hash_1497_; 
v_hash_1497_ = lean_ctor_get_uint64(v_x_1491_, sizeof(void*)*2);
v___y_1493_ = v_hash_1497_;
goto v___jp_1492_;
}
v___jp_1492_:
{
size_t v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = lean_uint64_to_usize(v___y_1493_);
v___x_1495_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg(v_x_1490_, v___x_1494_, v_x_1491_);
return v___x_1495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg___boxed(lean_object* v_x_1498_, lean_object* v_x_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v_x_1498_, v_x_1499_);
lean_dec(v_x_1499_);
lean_dec_ref(v_x_1498_);
return v_res_1500_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1503_ = ((lean_object*)(l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__1));
v___x_1504_ = ((lean_object*)(l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__0));
v___x_1505_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_1504_, v___x_1503_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclCore_x3f(uint8_t v_pu_1506_, lean_object* v_env_1507_, lean_object* v_ext_1508_, lean_object* v_declName_1509_){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1517_; 
v___x_1510_ = lean_obj_once(&l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2, &l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2_once, _init_l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2);
v___x_1517_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1507_, v_declName_1509_);
if (lean_obj_tag(v___x_1517_) == 0)
{
goto v___jp_1511_;
}
else
{
lean_object* v_val_1518_; lean_object* v_tmpDecl_1553_; lean_object* v_toSignature_1554_; lean_object* v_value_1555_; uint8_t v_recursive_1556_; lean_object* v_inlineAttr_x3f_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1584_; 
v_val_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_val_1518_);
lean_dec_ref_known(v___x_1517_, 1);
v_tmpDecl_1553_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default(v_pu_1506_);
v_toSignature_1554_ = lean_ctor_get(v_tmpDecl_1553_, 0);
v_value_1555_ = lean_ctor_get(v_tmpDecl_1553_, 1);
v_recursive_1556_ = lean_ctor_get_uint8(v_tmpDecl_1553_, sizeof(void*)*3);
v_inlineAttr_x3f_1557_ = lean_ctor_get(v_tmpDecl_1553_, 2);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_tmpDecl_1553_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1559_ = v_tmpDecl_1553_;
v_isShared_1560_ = v_isSharedCheck_1584_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_inlineAttr_x3f_1557_);
lean_inc(v_value_1555_);
lean_inc(v_toSignature_1554_);
lean_dec(v_tmpDecl_1553_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1584_;
goto v_resetjp_1558_;
}
v___jp_1519_:
{
lean_object* v_tmpDecl_1520_; lean_object* v_toSignature_1521_; lean_object* v_value_1522_; uint8_t v_recursive_1523_; lean_object* v_inlineAttr_x3f_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1552_; 
v_tmpDecl_1520_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default(v_pu_1506_);
v_toSignature_1521_ = lean_ctor_get(v_tmpDecl_1520_, 0);
v_value_1522_ = lean_ctor_get(v_tmpDecl_1520_, 1);
v_recursive_1523_ = lean_ctor_get_uint8(v_tmpDecl_1520_, sizeof(void*)*3);
v_inlineAttr_x3f_1524_ = lean_ctor_get(v_tmpDecl_1520_, 2);
v_isSharedCheck_1552_ = !lean_is_exclusive(v_tmpDecl_1520_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1526_ = v_tmpDecl_1520_;
v_isShared_1527_ = v_isSharedCheck_1552_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_inlineAttr_x3f_1524_);
lean_inc(v_value_1522_);
lean_inc(v_toSignature_1521_);
lean_dec(v_tmpDecl_1520_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1552_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v_levelParams_1528_; lean_object* v_type_1529_; lean_object* v_params_1530_; uint8_t v_safe_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1550_; 
v_levelParams_1528_ = lean_ctor_get(v_toSignature_1521_, 1);
v_type_1529_ = lean_ctor_get(v_toSignature_1521_, 2);
v_params_1530_ = lean_ctor_get(v_toSignature_1521_, 3);
v_safe_1531_ = lean_ctor_get_uint8(v_toSignature_1521_, sizeof(void*)*4);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_toSignature_1521_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; 
v_unused_1551_ = lean_ctor_get(v_toSignature_1521_, 0);
lean_dec(v_unused_1551_);
v___x_1533_ = v_toSignature_1521_;
v_isShared_1534_ = v_isSharedCheck_1550_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_params_1530_);
lean_inc(v_type_1529_);
lean_inc(v_levelParams_1528_);
lean_dec(v_toSignature_1521_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1550_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
uint8_t v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; 
v___x_1535_ = 0;
v___x_1536_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1510_, v_ext_1508_, v_env_1507_, v_val_1518_, v___x_1535_);
lean_dec(v_val_1518_);
v___x_1537_ = lean_unsigned_to_nat(0u);
v___x_1538_ = lean_array_get_size(v___x_1536_);
v___x_1539_ = lean_nat_dec_lt(v___x_1537_, v___x_1538_);
if (v___x_1539_ == 0)
{
lean_dec_ref(v___x_1536_);
lean_del_object(v___x_1533_);
lean_dec_ref(v_params_1530_);
lean_dec_ref(v_type_1529_);
lean_dec(v_levelParams_1528_);
lean_del_object(v___x_1526_);
lean_dec(v_inlineAttr_x3f_1524_);
lean_dec_ref(v_value_1522_);
goto v___jp_1511_;
}
else
{
lean_object* v___x_1540_; lean_object* v___x_1541_; uint8_t v___x_1542_; 
v___x_1540_ = lean_unsigned_to_nat(1u);
v___x_1541_ = lean_nat_sub(v___x_1538_, v___x_1540_);
v___x_1542_ = lean_nat_dec_le(v___x_1537_, v___x_1541_);
if (v___x_1542_ == 0)
{
lean_dec(v___x_1541_);
lean_dec_ref(v___x_1536_);
lean_del_object(v___x_1533_);
lean_dec_ref(v_params_1530_);
lean_dec_ref(v_type_1529_);
lean_dec(v_levelParams_1528_);
lean_del_object(v___x_1526_);
lean_dec(v_inlineAttr_x3f_1524_);
lean_dec_ref(v_value_1522_);
goto v___jp_1511_;
}
else
{
lean_object* v___x_1544_; 
lean_inc(v_declName_1509_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 0, v_declName_1509_);
v___x_1544_ = v___x_1533_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_declName_1509_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_levelParams_1528_);
lean_ctor_set(v_reuseFailAlloc_1549_, 2, v_type_1529_);
lean_ctor_set(v_reuseFailAlloc_1549_, 3, v_params_1530_);
lean_ctor_set_uint8(v_reuseFailAlloc_1549_, sizeof(void*)*4, v_safe_1531_);
v___x_1544_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v_tmpDecl_1546_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v___x_1544_);
v_tmpDecl_1546_ = v___x_1526_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1544_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_value_1522_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_inlineAttr_x3f_1524_);
lean_ctor_set_uint8(v_reuseFailAlloc_1548_, sizeof(void*)*3, v_recursive_1523_);
v_tmpDecl_1546_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(v___x_1536_, v_tmpDecl_1546_, v___x_1537_, v___x_1541_);
lean_dec_ref(v_tmpDecl_1546_);
lean_dec_ref(v___x_1536_);
if (lean_obj_tag(v___x_1547_) == 0)
{
goto v___jp_1511_;
}
else
{
lean_dec(v_declName_1509_);
lean_dec_ref(v_env_1507_);
return v___x_1547_;
}
}
}
}
}
}
}
}
v_resetjp_1558_:
{
lean_object* v_levelParams_1561_; lean_object* v_type_1562_; lean_object* v_params_1563_; uint8_t v_safe_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1582_; 
v_levelParams_1561_ = lean_ctor_get(v_toSignature_1554_, 1);
v_type_1562_ = lean_ctor_get(v_toSignature_1554_, 2);
v_params_1563_ = lean_ctor_get(v_toSignature_1554_, 3);
v_safe_1564_ = lean_ctor_get_uint8(v_toSignature_1554_, sizeof(void*)*4);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_toSignature_1554_);
if (v_isSharedCheck_1582_ == 0)
{
lean_object* v_unused_1583_; 
v_unused_1583_ = lean_ctor_get(v_toSignature_1554_, 0);
lean_dec(v_unused_1583_);
v___x_1566_ = v_toSignature_1554_;
v_isShared_1567_ = v_isSharedCheck_1582_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_params_1563_);
lean_inc(v_type_1562_);
lean_inc(v_levelParams_1561_);
lean_dec(v_toSignature_1554_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1582_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1568_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_1510_, v_ext_1508_, v_env_1507_, v_val_1518_);
v___x_1569_ = lean_unsigned_to_nat(0u);
v___x_1570_ = lean_array_get_size(v___x_1568_);
v___x_1571_ = lean_nat_dec_lt(v___x_1569_, v___x_1570_);
if (v___x_1571_ == 0)
{
lean_dec_ref(v___x_1568_);
lean_del_object(v___x_1566_);
lean_dec_ref(v_params_1563_);
lean_dec_ref(v_type_1562_);
lean_dec(v_levelParams_1561_);
lean_del_object(v___x_1559_);
lean_dec(v_inlineAttr_x3f_1557_);
lean_dec_ref(v_value_1555_);
goto v___jp_1519_;
}
else
{
lean_object* v___x_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; 
v___x_1572_ = lean_unsigned_to_nat(1u);
v___x_1573_ = lean_nat_sub(v___x_1570_, v___x_1572_);
v___x_1574_ = lean_nat_dec_le(v___x_1569_, v___x_1573_);
if (v___x_1574_ == 0)
{
lean_dec(v___x_1573_);
lean_dec_ref(v___x_1568_);
lean_del_object(v___x_1566_);
lean_dec_ref(v_params_1563_);
lean_dec_ref(v_type_1562_);
lean_dec(v_levelParams_1561_);
lean_del_object(v___x_1559_);
lean_dec(v_inlineAttr_x3f_1557_);
lean_dec_ref(v_value_1555_);
goto v___jp_1519_;
}
else
{
lean_object* v___x_1576_; 
lean_inc(v_declName_1509_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v_declName_1509_);
v___x_1576_ = v___x_1566_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_declName_1509_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_levelParams_1561_);
lean_ctor_set(v_reuseFailAlloc_1581_, 2, v_type_1562_);
lean_ctor_set(v_reuseFailAlloc_1581_, 3, v_params_1563_);
lean_ctor_set_uint8(v_reuseFailAlloc_1581_, sizeof(void*)*4, v_safe_1564_);
v___x_1576_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v_tmpDecl_1578_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v___x_1576_);
v_tmpDecl_1578_ = v___x_1559_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1576_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_value_1555_);
lean_ctor_set(v_reuseFailAlloc_1580_, 2, v_inlineAttr_x3f_1557_);
lean_ctor_set_uint8(v_reuseFailAlloc_1580_, sizeof(void*)*3, v_recursive_1556_);
v_tmpDecl_1578_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(v___x_1568_, v_tmpDecl_1578_, v___x_1569_, v___x_1573_);
lean_dec_ref(v_tmpDecl_1578_);
lean_dec_ref(v___x_1568_);
if (lean_obj_tag(v___x_1579_) == 0)
{
goto v___jp_1519_;
}
else
{
lean_dec(v_val_1518_);
lean_dec(v_declName_1509_);
lean_dec_ref(v_env_1507_);
return v___x_1579_;
}
}
}
}
}
}
}
}
v___jp_1511_:
{
lean_object* v_toEnvExtension_1512_; lean_object* v_asyncMode_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v_toEnvExtension_1512_ = lean_ctor_get(v_ext_1508_, 0);
v_asyncMode_1513_ = lean_ctor_get(v_toEnvExtension_1512_, 2);
v___x_1514_ = lean_box(0);
v___x_1515_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1510_, v_ext_1508_, v_env_1507_, v_asyncMode_1513_, v___x_1514_);
v___x_1516_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_1515_, v_declName_1509_);
lean_dec(v_declName_1509_);
lean_dec(v___x_1515_);
return v___x_1516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclCore_x3f___boxed(lean_object* v_pu_1585_, lean_object* v_env_1586_, lean_object* v_ext_1587_, lean_object* v_declName_1588_){
_start:
{
uint8_t v_pu_boxed_1589_; lean_object* v_res_1590_; 
v_pu_boxed_1589_ = lean_unbox(v_pu_1585_);
v_res_1590_ = l_Lean_Compiler_LCNF_getDeclCore_x3f(v_pu_boxed_1589_, v_env_1586_, v_ext_1587_, v_declName_1588_);
lean_dec_ref(v_ext_1587_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0(lean_object* v_00_u03b2_1591_, lean_object* v_x_1592_, lean_object* v_x_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v_x_1592_, v_x_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___boxed(lean_object* v_00_u03b2_1595_, lean_object* v_x_1596_, lean_object* v_x_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0(v_00_u03b2_1595_, v_x_1596_, v_x_1597_);
lean_dec(v_x_1597_);
lean_dec_ref(v_x_1596_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1(lean_object* v_as_1599_, lean_object* v_k_1600_, lean_object* v_x_1601_, lean_object* v_x_1602_, lean_object* v_x_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(v_as_1599_, v_k_1600_, v_x_1601_, v_x_1602_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___boxed(lean_object* v_as_1605_, lean_object* v_k_1606_, lean_object* v_x_1607_, lean_object* v_x_1608_, lean_object* v_x_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1(v_as_1605_, v_k_1606_, v_x_1607_, v_x_1608_, v_x_1609_);
lean_dec_ref(v_k_1606_);
lean_dec_ref(v_as_1605_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1611_, lean_object* v_x_1612_, size_t v_x_1613_, lean_object* v_x_1614_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg(v_x_1612_, v_x_1613_, v_x_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1616_, lean_object* v_x_1617_, lean_object* v_x_1618_, lean_object* v_x_1619_){
_start:
{
size_t v_x_623__boxed_1620_; lean_object* v_res_1621_; 
v_x_623__boxed_1620_ = lean_unbox_usize(v_x_1618_);
lean_dec(v_x_1618_);
v_res_1621_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0(v_00_u03b2_1616_, v_x_1617_, v_x_623__boxed_1620_, v_x_1619_);
lean_dec(v_x_1619_);
lean_dec_ref(v_x_1617_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1622_, lean_object* v_keys_1623_, lean_object* v_vals_1624_, lean_object* v_heq_1625_, lean_object* v_i_1626_, lean_object* v_k_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1623_, v_vals_1624_, v_i_1626_, v_k_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1629_, lean_object* v_keys_1630_, lean_object* v_vals_1631_, lean_object* v_heq_1632_, lean_object* v_i_1633_, lean_object* v_k_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1629_, v_keys_1630_, v_vals_1631_, v_heq_1632_, v_i_1633_, v_k_1634_);
lean_dec(v_k_1634_);
lean_dec_ref(v_vals_1631_);
lean_dec_ref(v_keys_1630_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(lean_object* v_as_1636_, lean_object* v_k_1637_, lean_object* v_x_1638_, lean_object* v_x_1639_){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v_m_1642_; lean_object* v_a_1643_; uint8_t v___x_1644_; 
v___x_1640_ = lean_nat_add(v_x_1638_, v_x_1639_);
v___x_1641_ = lean_unsigned_to_nat(1u);
v_m_1642_ = lean_nat_shiftr(v___x_1640_, v___x_1641_);
lean_dec(v___x_1640_);
v_a_1643_ = lean_array_fget_borrowed(v_as_1636_, v_m_1642_);
v___x_1644_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2(v_a_1643_, v_k_1637_);
if (v___x_1644_ == 0)
{
uint8_t v___x_1645_; 
lean_dec(v_x_1639_);
v___x_1645_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2(v_k_1637_, v_a_1643_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; 
lean_dec(v_m_1642_);
lean_dec(v_x_1638_);
lean_inc(v_a_1643_);
v___x_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1646_, 0, v_a_1643_);
return v___x_1646_;
}
else
{
lean_object* v___x_1647_; uint8_t v___x_1648_; 
v___x_1647_ = lean_unsigned_to_nat(0u);
v___x_1648_ = lean_nat_dec_eq(v_m_1642_, v___x_1647_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; uint8_t v___x_1650_; 
v___x_1649_ = lean_nat_sub(v_m_1642_, v___x_1641_);
lean_dec(v_m_1642_);
v___x_1650_ = lean_nat_dec_lt(v___x_1649_, v_x_1638_);
if (v___x_1650_ == 0)
{
v_x_1639_ = v___x_1649_;
goto _start;
}
else
{
lean_object* v___x_1652_; 
lean_dec(v___x_1649_);
lean_dec(v_x_1638_);
v___x_1652_ = lean_box(0);
return v___x_1652_;
}
}
else
{
lean_object* v___x_1653_; 
lean_dec(v_m_1642_);
lean_dec(v_x_1638_);
v___x_1653_ = lean_box(0);
return v___x_1653_;
}
}
}
else
{
lean_object* v___x_1654_; uint8_t v___x_1655_; 
lean_dec(v_x_1638_);
v___x_1654_ = lean_nat_add(v_m_1642_, v___x_1641_);
lean_dec(v_m_1642_);
v___x_1655_ = lean_nat_dec_le(v___x_1654_, v_x_1639_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; 
lean_dec(v___x_1654_);
lean_dec(v_x_1639_);
v___x_1656_ = lean_box(0);
return v___x_1656_;
}
else
{
v_x_1638_ = v___x_1654_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg___boxed(lean_object* v_as_1658_, lean_object* v_k_1659_, lean_object* v_x_1660_, lean_object* v_x_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(v_as_1658_, v_k_1659_, v_x_1660_, v_x_1661_);
lean_dec_ref(v_k_1659_);
lean_dec_ref(v_as_1658_);
return v_res_1662_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getSigCore_x3f___closed__0(void){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1663_ = ((lean_object*)(l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__1));
v___x_1664_ = ((lean_object*)(l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__0));
v___x_1665_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_1664_, v___x_1663_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSigCore_x3f(uint8_t v_pu_1666_, lean_object* v_env_1667_, lean_object* v_ext_1668_, lean_object* v_declName_1669_){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1677_; 
v___x_1670_ = lean_obj_once(&l_Lean_Compiler_LCNF_getSigCore_x3f___closed__0, &l_Lean_Compiler_LCNF_getSigCore_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_getSigCore_x3f___closed__0);
v___x_1677_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1667_, v_declName_1669_);
if (lean_obj_tag(v___x_1677_) == 0)
{
goto v___jp_1671_;
}
else
{
lean_object* v_val_1678_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; 
v_val_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_val_1678_);
lean_dec_ref_known(v___x_1677_, 1);
v___x_1702_ = l_Lean_PersistentEnvExtension_getModuleIREntries___redArg(v___x_1670_, v_ext_1668_, v_env_1667_, v_val_1678_);
v___x_1703_ = lean_unsigned_to_nat(0u);
v___x_1704_ = lean_array_get_size(v___x_1702_);
v___x_1705_ = lean_nat_dec_lt(v___x_1703_, v___x_1704_);
if (v___x_1705_ == 0)
{
lean_dec_ref(v___x_1702_);
goto v___jp_1679_;
}
else
{
lean_object* v_tmpSig_1706_; lean_object* v_levelParams_1707_; lean_object* v_type_1708_; lean_object* v_params_1709_; uint8_t v_safe_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1721_; 
v_tmpSig_1706_ = l_Lean_Compiler_LCNF_instInhabitedSignature_default(v_pu_1666_);
v_levelParams_1707_ = lean_ctor_get(v_tmpSig_1706_, 1);
v_type_1708_ = lean_ctor_get(v_tmpSig_1706_, 2);
v_params_1709_ = lean_ctor_get(v_tmpSig_1706_, 3);
v_safe_1710_ = lean_ctor_get_uint8(v_tmpSig_1706_, sizeof(void*)*4);
v_isSharedCheck_1721_ = !lean_is_exclusive(v_tmpSig_1706_);
if (v_isSharedCheck_1721_ == 0)
{
lean_object* v_unused_1722_; 
v_unused_1722_ = lean_ctor_get(v_tmpSig_1706_, 0);
lean_dec(v_unused_1722_);
v___x_1712_ = v_tmpSig_1706_;
v_isShared_1713_ = v_isSharedCheck_1721_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_params_1709_);
lean_inc(v_type_1708_);
lean_inc(v_levelParams_1707_);
lean_dec(v_tmpSig_1706_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1721_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; 
v___x_1714_ = lean_unsigned_to_nat(1u);
v___x_1715_ = lean_nat_sub(v___x_1704_, v___x_1714_);
v___x_1716_ = lean_nat_dec_le(v___x_1703_, v___x_1715_);
if (v___x_1716_ == 0)
{
lean_dec(v___x_1715_);
lean_del_object(v___x_1712_);
lean_dec_ref(v_params_1709_);
lean_dec_ref(v_type_1708_);
lean_dec(v_levelParams_1707_);
lean_dec_ref(v___x_1702_);
goto v___jp_1679_;
}
else
{
lean_object* v_tmpSig_1718_; 
lean_inc(v_declName_1669_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 0, v_declName_1669_);
v_tmpSig_1718_ = v___x_1712_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_declName_1669_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_levelParams_1707_);
lean_ctor_set(v_reuseFailAlloc_1720_, 2, v_type_1708_);
lean_ctor_set(v_reuseFailAlloc_1720_, 3, v_params_1709_);
lean_ctor_set_uint8(v_reuseFailAlloc_1720_, sizeof(void*)*4, v_safe_1710_);
v_tmpSig_1718_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(v___x_1702_, v_tmpSig_1718_, v___x_1703_, v___x_1715_);
lean_dec_ref(v_tmpSig_1718_);
lean_dec_ref(v___x_1702_);
if (lean_obj_tag(v___x_1719_) == 0)
{
goto v___jp_1679_;
}
else
{
lean_dec(v_val_1678_);
lean_dec(v_declName_1669_);
lean_dec_ref(v_env_1667_);
return v___x_1719_;
}
}
}
}
}
v___jp_1679_:
{
uint8_t v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; uint8_t v___x_1684_; 
v___x_1680_ = 0;
v___x_1681_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1670_, v_ext_1668_, v_env_1667_, v_val_1678_, v___x_1680_);
lean_dec(v_val_1678_);
v___x_1682_ = lean_unsigned_to_nat(0u);
v___x_1683_ = lean_array_get_size(v___x_1681_);
v___x_1684_ = lean_nat_dec_lt(v___x_1682_, v___x_1683_);
if (v___x_1684_ == 0)
{
lean_dec_ref(v___x_1681_);
goto v___jp_1671_;
}
else
{
lean_object* v_tmpSig_1685_; lean_object* v_levelParams_1686_; lean_object* v_type_1687_; lean_object* v_params_1688_; uint8_t v_safe_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1700_; 
v_tmpSig_1685_ = l_Lean_Compiler_LCNF_instInhabitedSignature_default(v_pu_1666_);
v_levelParams_1686_ = lean_ctor_get(v_tmpSig_1685_, 1);
v_type_1687_ = lean_ctor_get(v_tmpSig_1685_, 2);
v_params_1688_ = lean_ctor_get(v_tmpSig_1685_, 3);
v_safe_1689_ = lean_ctor_get_uint8(v_tmpSig_1685_, sizeof(void*)*4);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_tmpSig_1685_);
if (v_isSharedCheck_1700_ == 0)
{
lean_object* v_unused_1701_; 
v_unused_1701_ = lean_ctor_get(v_tmpSig_1685_, 0);
lean_dec(v_unused_1701_);
v___x_1691_ = v_tmpSig_1685_;
v_isShared_1692_ = v_isSharedCheck_1700_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_params_1688_);
lean_inc(v_type_1687_);
lean_inc(v_levelParams_1686_);
lean_dec(v_tmpSig_1685_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1700_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; 
v___x_1693_ = lean_unsigned_to_nat(1u);
v___x_1694_ = lean_nat_sub(v___x_1683_, v___x_1693_);
v___x_1695_ = lean_nat_dec_le(v___x_1682_, v___x_1694_);
if (v___x_1695_ == 0)
{
lean_dec(v___x_1694_);
lean_del_object(v___x_1691_);
lean_dec_ref(v_params_1688_);
lean_dec_ref(v_type_1687_);
lean_dec(v_levelParams_1686_);
lean_dec_ref(v___x_1681_);
goto v___jp_1671_;
}
else
{
lean_object* v_tmpSig_1697_; 
lean_inc(v_declName_1669_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v_declName_1669_);
v_tmpSig_1697_ = v___x_1691_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_declName_1669_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_levelParams_1686_);
lean_ctor_set(v_reuseFailAlloc_1699_, 2, v_type_1687_);
lean_ctor_set(v_reuseFailAlloc_1699_, 3, v_params_1688_);
lean_ctor_set_uint8(v_reuseFailAlloc_1699_, sizeof(void*)*4, v_safe_1689_);
v_tmpSig_1697_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(v___x_1681_, v_tmpSig_1697_, v___x_1682_, v___x_1694_);
lean_dec_ref(v_tmpSig_1697_);
lean_dec_ref(v___x_1681_);
if (lean_obj_tag(v___x_1698_) == 0)
{
goto v___jp_1671_;
}
else
{
lean_dec(v_declName_1669_);
lean_dec_ref(v_env_1667_);
return v___x_1698_;
}
}
}
}
}
}
}
v___jp_1671_:
{
lean_object* v_toEnvExtension_1672_; lean_object* v_asyncMode_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v_toEnvExtension_1672_ = lean_ctor_get(v_ext_1668_, 0);
v_asyncMode_1673_ = lean_ctor_get(v_toEnvExtension_1672_, 2);
v___x_1674_ = lean_box(0);
v___x_1675_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1670_, v_ext_1668_, v_env_1667_, v_asyncMode_1673_, v___x_1674_);
v___x_1676_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_1675_, v_declName_1669_);
lean_dec(v_declName_1669_);
lean_dec(v___x_1675_);
return v___x_1676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSigCore_x3f___boxed(lean_object* v_pu_1723_, lean_object* v_env_1724_, lean_object* v_ext_1725_, lean_object* v_declName_1726_){
_start:
{
uint8_t v_pu_boxed_1727_; lean_object* v_res_1728_; 
v_pu_boxed_1727_ = lean_unbox(v_pu_1723_);
v_res_1728_ = l_Lean_Compiler_LCNF_getSigCore_x3f(v_pu_boxed_1727_, v_env_1724_, v_ext_1725_, v_declName_1726_);
lean_dec_ref(v_ext_1725_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0(lean_object* v_as_1729_, lean_object* v_k_1730_, lean_object* v_x_1731_, lean_object* v_x_1732_, lean_object* v_x_1733_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(v_as_1729_, v_k_1730_, v_x_1731_, v_x_1732_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___boxed(lean_object* v_as_1735_, lean_object* v_k_1736_, lean_object* v_x_1737_, lean_object* v_x_1738_, lean_object* v_x_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0(v_as_1735_, v_k_1736_, v_x_1737_, v_x_1738_, v_x_1739_);
lean_dec_ref(v_k_1736_);
lean_dec_ref(v_as_1735_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg(lean_object* v_declName_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v___x_1744_; lean_object* v_env_1745_; uint8_t v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1744_ = lean_st_ref_get(v_a_1742_);
v_env_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc_ref(v_env_1745_);
lean_dec(v___x_1744_);
v___x_1746_ = 0;
v___x_1747_ = l_Lean_Compiler_LCNF_baseExt;
v___x_1748_ = l_Lean_Compiler_LCNF_getDeclCore_x3f(v___x_1746_, v_env_1745_, v___x_1747_, v_declName_1741_);
v___x_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg___boxed(lean_object* v_declName_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg(v_declName_1750_, v_a_1751_);
lean_dec(v_a_1751_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBaseDecl_x3f(lean_object* v_declName_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg(v_declName_1754_, v_a_1756_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBaseDecl_x3f___boxed(lean_object* v_declName_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Lean_Compiler_LCNF_getBaseDecl_x3f(v_declName_1759_, v_a_1760_, v_a_1761_);
lean_dec(v_a_1761_);
lean_dec_ref(v_a_1760_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(lean_object* v_declName_1764_, lean_object* v_a_1765_){
_start:
{
lean_object* v___x_1767_; lean_object* v_env_1768_; uint8_t v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1767_ = lean_st_ref_get(v_a_1765_);
v_env_1768_ = lean_ctor_get(v___x_1767_, 0);
lean_inc_ref(v_env_1768_);
lean_dec(v___x_1767_);
v___x_1769_ = 0;
v___x_1770_ = l_Lean_Compiler_LCNF_monoExt;
v___x_1771_ = l_Lean_Compiler_LCNF_getDeclCore_x3f(v___x_1769_, v_env_1768_, v___x_1770_, v_declName_1764_);
v___x_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg___boxed(lean_object* v_declName_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_1773_, v_a_1774_);
lean_dec(v_a_1774_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f(lean_object* v_declName_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_1777_, v_a_1779_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___boxed(lean_object* v_declName_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f(v_declName_1782_, v_a_1783_, v_a_1784_);
lean_dec(v_a_1784_);
lean_dec_ref(v_a_1783_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg(lean_object* v_declName_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v___x_1790_; lean_object* v_env_1791_; lean_object* v___x_1792_; lean_object* v_asyncMode_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1790_ = lean_st_ref_get(v_a_1788_);
v_env_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc_ref(v_env_1791_);
lean_dec(v___x_1790_);
v___x_1792_ = l_Lean_Compiler_LCNF_impureExt;
v_asyncMode_1793_ = lean_ctor_get(v___x_1792_, 2);
v___x_1794_ = lean_obj_once(&l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2, &l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2_once, _init_l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2);
v___x_1795_ = lean_box(0);
v___x_1796_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1794_, v___x_1792_, v_env_1791_, v_asyncMode_1793_, v___x_1795_);
v___x_1797_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_1796_, v_declName_1787_);
lean_dec(v___x_1796_);
v___x_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg___boxed(lean_object* v_declName_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg(v_declName_1799_, v_a_1800_);
lean_dec(v_a_1800_);
lean_dec(v_declName_1799_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f(lean_object* v_declName_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg(v_declName_1803_, v_a_1805_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___boxed(lean_object* v_declName_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f(v_declName_1808_, v_a_1809_, v_a_1810_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
lean_dec(v_declName_1808_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__1(size_t v_sz_1813_, size_t v_i_1814_, lean_object* v_bs_1815_){
_start:
{
uint8_t v___x_1816_; 
v___x_1816_ = lean_usize_dec_lt(v_i_1814_, v_sz_1813_);
if (v___x_1816_ == 0)
{
return v_bs_1815_;
}
else
{
lean_object* v_v_1817_; lean_object* v_fst_1818_; lean_object* v___x_1819_; lean_object* v_bs_x27_1820_; size_t v___x_1821_; size_t v___x_1822_; lean_object* v___x_1823_; 
v_v_1817_ = lean_array_uget_borrowed(v_bs_1815_, v_i_1814_);
v_fst_1818_ = lean_ctor_get(v_v_1817_, 0);
lean_inc(v_fst_1818_);
v___x_1819_ = lean_unsigned_to_nat(0u);
v_bs_x27_1820_ = lean_array_uset(v_bs_1815_, v_i_1814_, v___x_1819_);
v___x_1821_ = ((size_t)1ULL);
v___x_1822_ = lean_usize_add(v_i_1814_, v___x_1821_);
v___x_1823_ = lean_array_uset(v_bs_x27_1820_, v_i_1814_, v_fst_1818_);
v_i_1814_ = v___x_1822_;
v_bs_1815_ = v___x_1823_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__1___boxed(lean_object* v_sz_1825_, lean_object* v_i_1826_, lean_object* v_bs_1827_){
_start:
{
size_t v_sz_boxed_1828_; size_t v_i_boxed_1829_; lean_object* v_res_1830_; 
v_sz_boxed_1828_ = lean_unbox_usize(v_sz_1825_);
lean_dec(v_sz_1825_);
v_i_boxed_1829_ = lean_unbox_usize(v_i_1826_);
lean_dec(v_i_1826_);
v_res_1830_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__1(v_sz_boxed_1828_, v_i_boxed_1829_, v_bs_1827_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___lam__0(lean_object* v_ps_1831_, lean_object* v_k_1832_, lean_object* v_v_1833_){
_start:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1834_, 0, v_k_1832_);
lean_ctor_set(v___x_1834_, 1, v_v_1833_);
v___x_1835_ = lean_array_push(v_ps_1831_, v___x_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg(lean_object* v_m_1839_){
_start:
{
lean_object* v___f_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___f_1840_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__0));
v___x_1841_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__1));
v___x_1842_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_m_1839_, v___f_1840_, v___x_1841_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___boxed(lean_object* v_m_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg(v_m_1843_);
lean_dec_ref(v_m_1843_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecls___redArg(lean_object* v_a_1845_){
_start:
{
lean_object* v___x_1847_; lean_object* v_env_1848_; lean_object* v___x_1849_; lean_object* v_asyncMode_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; size_t v_sz_1855_; size_t v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1847_ = lean_st_ref_get(v_a_1845_);
v_env_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc_ref(v_env_1848_);
lean_dec(v___x_1847_);
v___x_1849_ = l_Lean_Compiler_LCNF_impureExt;
v_asyncMode_1850_ = lean_ctor_get(v___x_1849_, 2);
v___x_1851_ = lean_obj_once(&l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2, &l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2_once, _init_l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2);
v___x_1852_ = lean_box(0);
v___x_1853_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1851_, v___x_1849_, v_env_1848_, v_asyncMode_1850_, v___x_1852_);
v___x_1854_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg(v___x_1853_);
lean_dec(v___x_1853_);
v_sz_1855_ = lean_array_size(v___x_1854_);
v___x_1856_ = ((size_t)0ULL);
v___x_1857_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__1(v_sz_1855_, v___x_1856_, v___x_1854_);
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecls___redArg___boxed(lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Lean_Compiler_LCNF_getLocalImpureDecls___redArg(v_a_1859_);
lean_dec(v_a_1859_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecls(lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Lean_Compiler_LCNF_getLocalImpureDecls___redArg(v_a_1863_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecls___boxed(lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lean_Compiler_LCNF_getLocalImpureDecls(v_a_1866_, v_a_1867_);
lean_dec(v_a_1867_);
lean_dec_ref(v_a_1866_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0(lean_object* v_00_u03b2_1870_, lean_object* v_m_1871_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg(v_m_1871_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___boxed(lean_object* v_00_u03b2_1873_, lean_object* v_m_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0(v_00_u03b2_1873_, v_m_1874_);
lean_dec_ref(v_m_1874_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object* v_declName_1876_, lean_object* v_a_1877_){
_start:
{
lean_object* v___x_1879_; lean_object* v_env_1880_; uint8_t v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1879_ = lean_st_ref_get(v_a_1877_);
v_env_1880_ = lean_ctor_get(v___x_1879_, 0);
lean_inc_ref(v_env_1880_);
lean_dec(v___x_1879_);
v___x_1881_ = 1;
v___x_1882_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_1883_ = l_Lean_Compiler_LCNF_getSigCore_x3f(v___x_1881_, v_env_1880_, v___x_1882_, v_declName_1876_);
v___x_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg___boxed(lean_object* v_declName_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_1885_, v_a_1886_);
lean_dec(v_a_1886_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f(lean_object* v_declName_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_1889_, v_a_1891_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___boxed(lean_object* v_declName_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f(v_declName_1894_, v_a_1895_, v_a_1896_);
lean_dec(v_a_1896_);
lean_dec_ref(v_a_1895_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveBaseDeclCore(lean_object* v_env_1899_, lean_object* v_decl_1900_){
_start:
{
lean_object* v___x_1901_; lean_object* v_toEnvExtension_1902_; lean_object* v_asyncMode_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1901_ = l_Lean_Compiler_LCNF_baseExt;
v_toEnvExtension_1902_ = lean_ctor_get(v___x_1901_, 0);
v_asyncMode_1903_ = lean_ctor_get(v_toEnvExtension_1902_, 2);
v___x_1904_ = lean_box(0);
v___x_1905_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1901_, v_env_1899_, v_decl_1900_, v_asyncMode_1903_, v___x_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveMonoDeclCore(lean_object* v_env_1906_, lean_object* v_decl_1907_){
_start:
{
lean_object* v___x_1908_; lean_object* v_toEnvExtension_1909_; lean_object* v_asyncMode_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1908_ = l_Lean_Compiler_LCNF_monoExt;
v_toEnvExtension_1909_ = lean_ctor_get(v___x_1908_, 0);
v_asyncMode_1910_ = lean_ctor_get(v_toEnvExtension_1909_, 2);
v___x_1911_ = lean_box(0);
v___x_1912_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1908_, v_env_1906_, v_decl_1907_, v_asyncMode_1910_, v___x_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveImpureDeclCore___lam__0(lean_object* v_toSignature_1913_, lean_object* v_decl_1914_, lean_object* v_s_1915_){
_start:
{
lean_object* v_name_1916_; lean_object* v___x_1917_; 
v_name_1916_ = lean_ctor_get(v_toSignature_1913_, 0);
lean_inc(v_name_1916_);
lean_dec_ref(v_toSignature_1913_);
v___x_1917_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_s_1915_, v_name_1916_, v_decl_1914_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveImpureDeclCore(lean_object* v_env_1918_, lean_object* v_decl_1919_){
_start:
{
lean_object* v___x_1920_; lean_object* v_asyncMode_1921_; lean_object* v_toSignature_1922_; lean_object* v___x_1923_; lean_object* v_toEnvExtension_1924_; lean_object* v_asyncMode_1925_; lean_object* v___f_1926_; lean_object* v___x_1927_; lean_object* v_env_1928_; lean_object* v___x_1929_; 
v___x_1920_ = l_Lean_Compiler_LCNF_impureExt;
v_asyncMode_1921_ = lean_ctor_get(v___x_1920_, 2);
v_toSignature_1922_ = lean_ctor_get(v_decl_1919_, 0);
lean_inc_ref_n(v_toSignature_1922_, 2);
v___x_1923_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_1924_ = lean_ctor_get(v___x_1923_, 0);
v_asyncMode_1925_ = lean_ctor_get(v_toEnvExtension_1924_, 2);
v___f_1926_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_saveImpureDeclCore___lam__0), 3, 2);
lean_closure_set(v___f_1926_, 0, v_toSignature_1922_);
lean_closure_set(v___f_1926_, 1, v_decl_1919_);
v___x_1927_ = lean_box(0);
v_env_1928_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1920_, v_env_1918_, v___f_1926_, v_asyncMode_1921_, v___x_1927_);
v___x_1929_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1923_, v_env_1928_, v_toSignature_1922_, v_asyncMode_1925_, v___x_1927_);
return v___x_1929_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0(void){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1930_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1(void){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0, &l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0);
v___x_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
return v___x_1932_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1, &l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1);
v___x_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___redArg(lean_object* v_decl_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v___x_1938_; lean_object* v_env_1939_; lean_object* v_nextMacroScope_1940_; lean_object* v_ngen_1941_; lean_object* v_auxDeclNGen_1942_; lean_object* v_traceState_1943_; lean_object* v_messages_1944_; lean_object* v_infoState_1945_; lean_object* v_snapshotTasks_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1958_; 
v___x_1938_ = lean_st_ref_take(v_a_1936_);
v_env_1939_ = lean_ctor_get(v___x_1938_, 0);
v_nextMacroScope_1940_ = lean_ctor_get(v___x_1938_, 1);
v_ngen_1941_ = lean_ctor_get(v___x_1938_, 2);
v_auxDeclNGen_1942_ = lean_ctor_get(v___x_1938_, 3);
v_traceState_1943_ = lean_ctor_get(v___x_1938_, 4);
v_messages_1944_ = lean_ctor_get(v___x_1938_, 6);
v_infoState_1945_ = lean_ctor_get(v___x_1938_, 7);
v_snapshotTasks_1946_ = lean_ctor_get(v___x_1938_, 8);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1958_ == 0)
{
lean_object* v_unused_1959_; 
v_unused_1959_ = lean_ctor_get(v___x_1938_, 5);
lean_dec(v_unused_1959_);
v___x_1948_ = v___x_1938_;
v_isShared_1949_ = v_isSharedCheck_1958_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_snapshotTasks_1946_);
lean_inc(v_infoState_1945_);
lean_inc(v_messages_1944_);
lean_inc(v_traceState_1943_);
lean_inc(v_auxDeclNGen_1942_);
lean_inc(v_ngen_1941_);
lean_inc(v_nextMacroScope_1940_);
lean_inc(v_env_1939_);
lean_dec(v___x_1938_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1958_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1953_; 
v___x_1950_ = l_Lean_Compiler_LCNF_saveBaseDeclCore(v_env_1939_, v_decl_1935_);
v___x_1951_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2, &l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 5, v___x_1951_);
lean_ctor_set(v___x_1948_, 0, v___x_1950_);
v___x_1953_ = v___x_1948_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1950_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_nextMacroScope_1940_);
lean_ctor_set(v_reuseFailAlloc_1957_, 2, v_ngen_1941_);
lean_ctor_set(v_reuseFailAlloc_1957_, 3, v_auxDeclNGen_1942_);
lean_ctor_set(v_reuseFailAlloc_1957_, 4, v_traceState_1943_);
lean_ctor_set(v_reuseFailAlloc_1957_, 5, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_1957_, 6, v_messages_1944_);
lean_ctor_set(v_reuseFailAlloc_1957_, 7, v_infoState_1945_);
lean_ctor_set(v_reuseFailAlloc_1957_, 8, v_snapshotTasks_1946_);
v___x_1953_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1954_ = lean_st_ref_set(v_a_1936_, v___x_1953_);
v___x_1955_ = lean_box(0);
v___x_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1955_);
return v___x_1956_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___redArg___boxed(lean_object* v_decl_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(v_decl_1960_, v_a_1961_);
lean_dec(v_a_1961_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveBase(lean_object* v_decl_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_){
_start:
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(v_decl_1964_, v_a_1966_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___boxed(lean_object* v_decl_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Lean_Compiler_LCNF_Decl_saveBase(v_decl_1969_, v_a_1970_, v_a_1971_);
lean_dec(v_a_1971_);
lean_dec_ref(v_a_1970_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg(lean_object* v_decl_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v___x_1977_; lean_object* v_env_1978_; lean_object* v_nextMacroScope_1979_; lean_object* v_ngen_1980_; lean_object* v_auxDeclNGen_1981_; lean_object* v_traceState_1982_; lean_object* v_messages_1983_; lean_object* v_infoState_1984_; lean_object* v_snapshotTasks_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1997_; 
v___x_1977_ = lean_st_ref_take(v_a_1975_);
v_env_1978_ = lean_ctor_get(v___x_1977_, 0);
v_nextMacroScope_1979_ = lean_ctor_get(v___x_1977_, 1);
v_ngen_1980_ = lean_ctor_get(v___x_1977_, 2);
v_auxDeclNGen_1981_ = lean_ctor_get(v___x_1977_, 3);
v_traceState_1982_ = lean_ctor_get(v___x_1977_, 4);
v_messages_1983_ = lean_ctor_get(v___x_1977_, 6);
v_infoState_1984_ = lean_ctor_get(v___x_1977_, 7);
v_snapshotTasks_1985_ = lean_ctor_get(v___x_1977_, 8);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1997_ == 0)
{
lean_object* v_unused_1998_; 
v_unused_1998_ = lean_ctor_get(v___x_1977_, 5);
lean_dec(v_unused_1998_);
v___x_1987_ = v___x_1977_;
v_isShared_1988_ = v_isSharedCheck_1997_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_snapshotTasks_1985_);
lean_inc(v_infoState_1984_);
lean_inc(v_messages_1983_);
lean_inc(v_traceState_1982_);
lean_inc(v_auxDeclNGen_1981_);
lean_inc(v_ngen_1980_);
lean_inc(v_nextMacroScope_1979_);
lean_inc(v_env_1978_);
lean_dec(v___x_1977_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1997_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1992_; 
v___x_1989_ = l_Lean_Compiler_LCNF_saveMonoDeclCore(v_env_1978_, v_decl_1974_);
v___x_1990_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2, &l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 5, v___x_1990_);
lean_ctor_set(v___x_1987_, 0, v___x_1989_);
v___x_1992_ = v___x_1987_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v_nextMacroScope_1979_);
lean_ctor_set(v_reuseFailAlloc_1996_, 2, v_ngen_1980_);
lean_ctor_set(v_reuseFailAlloc_1996_, 3, v_auxDeclNGen_1981_);
lean_ctor_set(v_reuseFailAlloc_1996_, 4, v_traceState_1982_);
lean_ctor_set(v_reuseFailAlloc_1996_, 5, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_1996_, 6, v_messages_1983_);
lean_ctor_set(v_reuseFailAlloc_1996_, 7, v_infoState_1984_);
lean_ctor_set(v_reuseFailAlloc_1996_, 8, v_snapshotTasks_1985_);
v___x_1992_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1993_ = lean_st_ref_set(v_a_1975_, v___x_1992_);
v___x_1994_ = lean_box(0);
v___x_1995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1994_);
return v___x_1995_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg___boxed(lean_object* v_decl_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v_decl_1999_, v_a_2000_);
lean_dec(v_a_2000_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveMono(lean_object* v_decl_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v_decl_2003_, v_a_2005_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___boxed(lean_object* v_decl_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l_Lean_Compiler_LCNF_Decl_saveMono(v_decl_2008_, v_a_2009_, v_a_2010_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(lean_object* v_decl_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v___x_2016_; lean_object* v_env_2017_; lean_object* v_nextMacroScope_2018_; lean_object* v_ngen_2019_; lean_object* v_auxDeclNGen_2020_; lean_object* v_traceState_2021_; lean_object* v_messages_2022_; lean_object* v_infoState_2023_; lean_object* v_snapshotTasks_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2036_; 
v___x_2016_ = lean_st_ref_take(v_a_2014_);
v_env_2017_ = lean_ctor_get(v___x_2016_, 0);
v_nextMacroScope_2018_ = lean_ctor_get(v___x_2016_, 1);
v_ngen_2019_ = lean_ctor_get(v___x_2016_, 2);
v_auxDeclNGen_2020_ = lean_ctor_get(v___x_2016_, 3);
v_traceState_2021_ = lean_ctor_get(v___x_2016_, 4);
v_messages_2022_ = lean_ctor_get(v___x_2016_, 6);
v_infoState_2023_ = lean_ctor_get(v___x_2016_, 7);
v_snapshotTasks_2024_ = lean_ctor_get(v___x_2016_, 8);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2036_ == 0)
{
lean_object* v_unused_2037_; 
v_unused_2037_ = lean_ctor_get(v___x_2016_, 5);
lean_dec(v_unused_2037_);
v___x_2026_ = v___x_2016_;
v_isShared_2027_ = v_isSharedCheck_2036_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_snapshotTasks_2024_);
lean_inc(v_infoState_2023_);
lean_inc(v_messages_2022_);
lean_inc(v_traceState_2021_);
lean_inc(v_auxDeclNGen_2020_);
lean_inc(v_ngen_2019_);
lean_inc(v_nextMacroScope_2018_);
lean_inc(v_env_2017_);
lean_dec(v___x_2016_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2036_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2031_; 
v___x_2028_ = l_Lean_Compiler_LCNF_saveImpureDeclCore(v_env_2017_, v_decl_2013_);
v___x_2029_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2, &l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 5, v___x_2029_);
lean_ctor_set(v___x_2026_, 0, v___x_2028_);
v___x_2031_ = v___x_2026_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2028_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_nextMacroScope_2018_);
lean_ctor_set(v_reuseFailAlloc_2035_, 2, v_ngen_2019_);
lean_ctor_set(v_reuseFailAlloc_2035_, 3, v_auxDeclNGen_2020_);
lean_ctor_set(v_reuseFailAlloc_2035_, 4, v_traceState_2021_);
lean_ctor_set(v_reuseFailAlloc_2035_, 5, v___x_2029_);
lean_ctor_set(v_reuseFailAlloc_2035_, 6, v_messages_2022_);
lean_ctor_set(v_reuseFailAlloc_2035_, 7, v_infoState_2023_);
lean_ctor_set(v_reuseFailAlloc_2035_, 8, v_snapshotTasks_2024_);
v___x_2031_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2032_ = lean_st_ref_set(v_a_2014_, v___x_2031_);
v___x_2033_ = lean_box(0);
v___x_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
return v___x_2034_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___redArg___boxed(lean_object* v_decl_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_decl_2038_, v_a_2039_);
lean_dec(v_a_2039_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure(lean_object* v_decl_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_decl_2042_, v_a_2044_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___boxed(lean_object* v_decl_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Lean_Compiler_LCNF_Decl_saveImpure(v_decl_2047_, v_a_2048_, v_a_2049_);
lean_dec(v_a_2049_);
lean_dec_ref(v_a_2048_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__0(lean_object* v_decl_2052_, lean_object* v_h_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(v_decl_2052_, v___y_2057_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__0___boxed(lean_object* v_decl_2060_, lean_object* v_h_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Lean_Compiler_LCNF_Decl_save___lam__0(v_decl_2060_, v_h_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__1(lean_object* v_decl_2068_, lean_object* v_h_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v___x_2075_; 
v___x_2075_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v_decl_2068_, v___y_2073_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__1___boxed(lean_object* v_decl_2076_, lean_object* v_h_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Lean_Compiler_LCNF_Decl_save___lam__1(v_decl_2076_, v_h_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__2(lean_object* v_decl_2084_, lean_object* v_h_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_decl_2084_, v___y_2089_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__2___boxed(lean_object* v_decl_2092_, lean_object* v_h_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Lean_Compiler_LCNF_Decl_save___lam__2(v_decl_2092_, v_h_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
return v_res_2099_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_save___closed__0(void){
_start:
{
lean_object* v___x_2100_; 
v___x_2100_ = l_instMonadEIO(lean_box(0));
return v___x_2100_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_save___closed__1(void){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_save___closed__0, &l_Lean_Compiler_LCNF_Decl_save___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_save___closed__0);
v___x_2102_ = l_StateRefT_x27_instMonad___redArg(v___x_2101_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save(uint8_t v_pu_2105_, lean_object* v_decl_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_){
_start:
{
lean_object* v___x_2112_; lean_object* v_toApplicative_2113_; lean_object* v_toFunctor_2114_; lean_object* v_toSeq_2115_; lean_object* v_toSeqLeft_2116_; lean_object* v_toSeqRight_2117_; lean_object* v___f_2118_; lean_object* v___f_2119_; lean_object* v___f_2120_; lean_object* v___f_2121_; lean_object* v___x_2122_; lean_object* v___f_2123_; lean_object* v___f_2124_; lean_object* v___f_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2112_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_save___closed__1, &l_Lean_Compiler_LCNF_Decl_save___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_save___closed__1);
v_toApplicative_2113_ = lean_ctor_get(v___x_2112_, 0);
v_toFunctor_2114_ = lean_ctor_get(v_toApplicative_2113_, 0);
v_toSeq_2115_ = lean_ctor_get(v_toApplicative_2113_, 2);
v_toSeqLeft_2116_ = lean_ctor_get(v_toApplicative_2113_, 3);
v_toSeqRight_2117_ = lean_ctor_get(v_toApplicative_2113_, 4);
v___f_2118_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_save___closed__2));
v___f_2119_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_save___closed__3));
lean_inc_ref_n(v_toFunctor_2114_, 2);
v___f_2120_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2120_, 0, v_toFunctor_2114_);
v___f_2121_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2121_, 0, v_toFunctor_2114_);
v___x_2122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___f_2120_);
lean_ctor_set(v___x_2122_, 1, v___f_2121_);
lean_inc(v_toSeqRight_2117_);
v___f_2123_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2123_, 0, v_toSeqRight_2117_);
lean_inc(v_toSeqLeft_2116_);
v___f_2124_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2124_, 0, v_toSeqLeft_2116_);
lean_inc(v_toSeq_2115_);
v___f_2125_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2125_, 0, v_toSeq_2115_);
v___x_2126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2122_);
lean_ctor_set(v___x_2126_, 1, v___f_2118_);
lean_ctor_set(v___x_2126_, 2, v___f_2125_);
lean_ctor_set(v___x_2126_, 3, v___f_2124_);
lean_ctor_set(v___x_2126_, 4, v___f_2123_);
v___x_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
lean_ctor_set(v___x_2127_, 1, v___f_2119_);
v___x_2128_ = l_StateRefT_x27_instMonad___redArg(v___x_2127_);
v___x_2129_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_2107_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___f_2133_; uint8_t v___x_2134_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2129_, 1);
v___x_2131_ = lean_box(0);
v___x_2132_ = l_instInhabitedOfMonad___redArg(v___x_2128_, v___x_2131_);
v___f_2133_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2133_, 0, v___x_2132_);
v___x_2134_ = lean_unbox(v_a_2130_);
switch(v___x_2134_)
{
case 0:
{
lean_object* v___f_2135_; uint8_t v___x_2136_; lean_object* v___x_380__overap_2137_; lean_object* v___x_2138_; 
v___f_2135_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_save___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2135_, 0, v_decl_2106_);
v___x_2136_ = lean_unbox(v_a_2130_);
lean_dec(v_a_2130_);
v___x_380__overap_2137_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___f_2133_, v___x_2136_, v_pu_2105_, v___f_2135_);
lean_dec_ref(v___f_2133_);
lean_inc(v_a_2110_);
lean_inc_ref(v_a_2109_);
lean_inc(v_a_2108_);
lean_inc_ref(v_a_2107_);
v___x_2138_ = lean_apply_5(v___x_380__overap_2137_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, lean_box(0));
return v___x_2138_;
}
case 1:
{
lean_object* v___f_2139_; uint8_t v___x_2140_; lean_object* v___x_398__overap_2141_; lean_object* v___x_2142_; 
v___f_2139_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_save___lam__1___boxed), 7, 1);
lean_closure_set(v___f_2139_, 0, v_decl_2106_);
v___x_2140_ = lean_unbox(v_a_2130_);
lean_dec(v_a_2130_);
v___x_398__overap_2141_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___f_2133_, v___x_2140_, v_pu_2105_, v___f_2139_);
lean_dec_ref(v___f_2133_);
lean_inc(v_a_2110_);
lean_inc_ref(v_a_2109_);
lean_inc(v_a_2108_);
lean_inc_ref(v_a_2107_);
v___x_2142_ = lean_apply_5(v___x_398__overap_2141_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, lean_box(0));
return v___x_2142_;
}
default: 
{
lean_object* v___f_2143_; uint8_t v___x_2144_; lean_object* v___x_416__overap_2145_; lean_object* v___x_2146_; 
v___f_2143_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_save___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2143_, 0, v_decl_2106_);
v___x_2144_ = lean_unbox(v_a_2130_);
lean_dec(v_a_2130_);
v___x_416__overap_2145_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___f_2133_, v___x_2144_, v_pu_2105_, v___f_2143_);
lean_dec_ref(v___f_2133_);
lean_inc(v_a_2110_);
lean_inc_ref(v_a_2109_);
lean_inc(v_a_2108_);
lean_inc_ref(v_a_2107_);
v___x_2146_ = lean_apply_5(v___x_416__overap_2145_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, lean_box(0));
return v___x_2146_;
}
}
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_dec_ref(v___x_2128_);
lean_dec_ref(v_decl_2106_);
v_a_2147_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2129_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2129_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___boxed(lean_object* v_pu_2155_, lean_object* v_decl_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_){
_start:
{
uint8_t v_pu_boxed_2162_; lean_object* v_res_2163_; 
v_pu_boxed_2162_ = lean_unbox(v_pu_2155_);
v_res_2163_ = l_Lean_Compiler_LCNF_Decl_save(v_pu_boxed_2162_, v_decl_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
lean_dec(v_a_2160_);
lean_dec_ref(v_a_2159_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
return v_res_2163_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2164_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0);
v___x_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
return v___x_2166_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2167_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1);
v___x_2168_ = lean_unsigned_to_nat(0u);
v___x_2169_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
lean_ctor_set(v___x_2169_, 2, v___x_2168_);
lean_ctor_set(v___x_2169_, 3, v___x_2168_);
lean_ctor_set(v___x_2169_, 4, v___x_2167_);
lean_ctor_set(v___x_2169_, 5, v___x_2167_);
lean_ctor_set(v___x_2169_, 6, v___x_2167_);
lean_ctor_set(v___x_2169_, 7, v___x_2167_);
lean_ctor_set(v___x_2169_, 8, v___x_2167_);
lean_ctor_set(v___x_2169_, 9, v___x_2167_);
return v___x_2169_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2170_ = lean_unsigned_to_nat(32u);
v___x_2171_ = lean_mk_empty_array_with_capacity(v___x_2170_);
v___x_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
return v___x_2172_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2173_ = ((size_t)5ULL);
v___x_2174_ = lean_unsigned_to_nat(0u);
v___x_2175_ = lean_unsigned_to_nat(32u);
v___x_2176_ = lean_mk_empty_array_with_capacity(v___x_2175_);
v___x_2177_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3);
v___x_2178_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2178_, 0, v___x_2177_);
lean_ctor_set(v___x_2178_, 1, v___x_2176_);
lean_ctor_set(v___x_2178_, 2, v___x_2174_);
lean_ctor_set(v___x_2178_, 3, v___x_2174_);
lean_ctor_set_usize(v___x_2178_, 4, v___x_2173_);
return v___x_2178_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2179_ = lean_box(1);
v___x_2180_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4);
v___x_2181_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1);
v___x_2182_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
lean_ctor_set(v___x_2182_, 1, v___x_2180_);
lean_ctor_set(v___x_2182_, 2, v___x_2179_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0(lean_object* v_msgData_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v___x_2187_; lean_object* v_env_2188_; lean_object* v_options_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2187_ = lean_st_ref_get(v___y_2185_);
v_env_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc_ref(v_env_2188_);
lean_dec(v___x_2187_);
v_options_2189_ = lean_ctor_get(v___y_2184_, 2);
v___x_2190_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2);
v___x_2191_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_2189_);
v___x_2192_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2192_, 0, v_env_2188_);
lean_ctor_set(v___x_2192_, 1, v___x_2190_);
lean_ctor_set(v___x_2192_, 2, v___x_2191_);
lean_ctor_set(v___x_2192_, 3, v_options_2189_);
v___x_2193_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
lean_ctor_set(v___x_2193_, 1, v_msgData_2183_);
v___x_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___boxed(lean_object* v_msgData_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0(v_msgData_2195_, v___y_2196_, v___y_2197_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg(lean_object* v_msg_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v_ref_2204_; lean_object* v___x_2205_; lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2214_; 
v_ref_2204_ = lean_ctor_get(v___y_2201_, 5);
v___x_2205_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0(v_msg_2200_, v___y_2201_, v___y_2202_);
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2208_ = v___x_2205_;
v_isShared_2209_ = v_isSharedCheck_2214_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2205_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2214_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; lean_object* v___x_2212_; 
lean_inc(v_ref_2204_);
v___x_2210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2210_, 0, v_ref_2204_);
lean_ctor_set(v___x_2210_, 1, v_a_2206_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set_tag(v___x_2208_, 1);
lean_ctor_set(v___x_2208_, 0, v___x_2210_);
v___x_2212_ = v___x_2208_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2210_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg___boxed(lean_object* v_msg_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg(v_msg_2215_, v___y_2216_, v___y_2217_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
return v_res_2219_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1(void){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = ((lean_object*)(l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__0));
v___x_2222_ = l_Lean_stringToMessageData(v___x_2221_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f(lean_object* v_declName_2223_, uint8_t v_phase_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_){
_start:
{
switch(v_phase_2224_)
{
case 0:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg(v_declName_2223_, v_a_2226_);
return v___x_2228_;
}
case 1:
{
lean_object* v___x_2229_; 
v___x_2229_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_2223_, v_a_2226_);
return v___x_2229_;
}
default: 
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
lean_dec(v_declName_2223_);
v___x_2230_ = lean_obj_once(&l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1, &l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1_once, _init_l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1);
v___x_2231_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg(v___x_2230_, v_a_2225_, v_a_2226_);
return v___x_2231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f___boxed(lean_object* v_declName_2232_, lean_object* v_phase_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_){
_start:
{
uint8_t v_phase_boxed_2237_; lean_object* v_res_2238_; 
v_phase_boxed_2237_ = lean_unbox(v_phase_2233_);
v_res_2238_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_2232_, v_phase_boxed_2237_, v_a_2234_, v_a_2235_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0(lean_object* v_00_u03b1_2239_, lean_object* v_msg_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg(v_msg_2240_, v___y_2241_, v___y_2242_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___boxed(lean_object* v_00_u03b1_2245_, lean_object* v_msg_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0(v_00_u03b1_2245_, v_msg_2246_, v___y_2247_, v___y_2248_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg(lean_object* v_declName_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_2252_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; uint8_t v___x_2258_; lean_object* v___x_2259_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2257_);
lean_dec_ref_known(v___x_2256_, 1);
v___x_2258_ = lean_unbox(v_a_2257_);
v___x_2259_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_2251_, v___x_2258_, v_a_2253_, v_a_2254_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2283_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2262_ = v___x_2259_;
v_isShared_2263_ = v_isSharedCheck_2283_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2259_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2283_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
if (lean_obj_tag(v_a_2260_) == 1)
{
lean_object* v_val_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2278_; 
v_val_2264_ = lean_ctor_get(v_a_2260_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v_a_2260_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2266_ = v_a_2260_;
v_isShared_2267_ = v_isSharedCheck_2278_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_val_2264_);
lean_dec(v_a_2260_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2278_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
uint8_t v___x_2268_; uint8_t v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2273_; 
v___x_2268_ = lean_unbox(v_a_2257_);
lean_dec(v_a_2257_);
v___x_2269_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_2268_);
v___x_2270_ = lean_box(v___x_2269_);
v___x_2271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
lean_ctor_set(v___x_2271_, 1, v_val_2264_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 0, v___x_2271_);
v___x_2273_ = v___x_2266_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2271_);
v___x_2273_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
lean_object* v___x_2275_; 
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 0, v___x_2273_);
v___x_2275_ = v___x_2262_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2273_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
else
{
lean_object* v___x_2279_; lean_object* v___x_2281_; 
lean_dec(v_a_2260_);
lean_dec(v_a_2257_);
v___x_2279_ = lean_box(0);
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 0, v___x_2279_);
v___x_2281_ = v___x_2262_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2279_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_dec(v_a_2257_);
v_a_2284_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2259_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2259_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec(v_declName_2251_);
v_a_2292_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2256_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2256_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg___boxed(lean_object* v_declName_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(v_declName_2300_, v_a_2301_, v_a_2302_, v_a_2303_);
lean_dec(v_a_2303_);
lean_dec_ref(v_a_2302_);
lean_dec_ref(v_a_2301_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDecl_x3f(lean_object* v_declName_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_2307_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; uint8_t v___x_2314_; lean_object* v___x_2315_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2313_);
lean_dec_ref_known(v___x_2312_, 1);
v___x_2314_ = lean_unbox(v_a_2313_);
v___x_2315_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_2306_, v___x_2314_, v_a_2309_, v_a_2310_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2339_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2318_ = v___x_2315_;
v_isShared_2319_ = v_isSharedCheck_2339_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2339_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
if (lean_obj_tag(v_a_2316_) == 1)
{
lean_object* v_val_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2334_; 
v_val_2320_ = lean_ctor_get(v_a_2316_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_a_2316_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2322_ = v_a_2316_;
v_isShared_2323_ = v_isSharedCheck_2334_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_val_2320_);
lean_dec(v_a_2316_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2334_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
uint8_t v___x_2324_; uint8_t v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2329_; 
v___x_2324_ = lean_unbox(v_a_2313_);
lean_dec(v_a_2313_);
v___x_2325_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_2324_);
v___x_2326_ = lean_box(v___x_2325_);
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
lean_ctor_set(v___x_2327_, 1, v_val_2320_);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 0, v___x_2327_);
v___x_2329_ = v___x_2322_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2327_);
v___x_2329_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
lean_object* v___x_2331_; 
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v___x_2329_);
v___x_2331_ = v___x_2318_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
else
{
lean_object* v___x_2335_; lean_object* v___x_2337_; 
lean_dec(v_a_2316_);
lean_dec(v_a_2313_);
v___x_2335_ = lean_box(0);
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v___x_2335_);
v___x_2337_ = v___x_2318_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2335_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec(v_a_2313_);
v_a_2340_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2315_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2315_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
else
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
lean_dec(v_declName_2306_);
v_a_2348_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2312_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2312_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2353_; 
if (v_isShared_2351_ == 0)
{
v___x_2353_ = v___x_2350_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2348_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___boxed(lean_object* v_declName_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Lean_Compiler_LCNF_getDecl_x3f(v_declName_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(lean_object* v_declName_2363_, uint8_t v_phase_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = lean_obj_once(&l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2, &l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2_once, _init_l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2);
switch(v_phase_2364_)
{
case 0:
{
lean_object* v___x_2368_; lean_object* v_env_2369_; lean_object* v___x_2370_; lean_object* v_toEnvExtension_2371_; lean_object* v_asyncMode_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2368_ = lean_st_ref_get(v_a_2365_);
v_env_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc_ref(v_env_2369_);
lean_dec(v___x_2368_);
v___x_2370_ = l_Lean_Compiler_LCNF_baseExt;
v_toEnvExtension_2371_ = lean_ctor_get(v___x_2370_, 0);
v_asyncMode_2372_ = lean_ctor_get(v_toEnvExtension_2371_, 2);
v___x_2373_ = lean_box(0);
v___x_2374_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2367_, v___x_2370_, v_env_2369_, v_asyncMode_2372_, v___x_2373_);
v___x_2375_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_2374_, v_declName_2363_);
lean_dec(v___x_2374_);
v___x_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
return v___x_2376_;
}
case 1:
{
lean_object* v___x_2377_; lean_object* v_env_2378_; lean_object* v___x_2379_; lean_object* v_toEnvExtension_2380_; lean_object* v_asyncMode_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2377_ = lean_st_ref_get(v_a_2365_);
v_env_2378_ = lean_ctor_get(v___x_2377_, 0);
lean_inc_ref(v_env_2378_);
lean_dec(v___x_2377_);
v___x_2379_ = l_Lean_Compiler_LCNF_monoExt;
v_toEnvExtension_2380_ = lean_ctor_get(v___x_2379_, 0);
v_asyncMode_2381_ = lean_ctor_get(v_toEnvExtension_2380_, 2);
v___x_2382_ = lean_box(0);
v___x_2383_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2367_, v___x_2379_, v_env_2378_, v_asyncMode_2381_, v___x_2382_);
v___x_2384_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_2383_, v_declName_2363_);
lean_dec(v___x_2383_);
v___x_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2384_);
return v___x_2385_;
}
default: 
{
lean_object* v___x_2386_; lean_object* v_env_2387_; lean_object* v___x_2388_; lean_object* v_asyncMode_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2386_ = lean_st_ref_get(v_a_2365_);
v_env_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc_ref(v_env_2387_);
lean_dec(v___x_2386_);
v___x_2388_ = l_Lean_Compiler_LCNF_impureExt;
v_asyncMode_2389_ = lean_ctor_get(v___x_2388_, 2);
v___x_2390_ = lean_box(0);
v___x_2391_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2367_, v___x_2388_, v_env_2387_, v_asyncMode_2389_, v___x_2390_);
v___x_2392_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_2391_, v_declName_2363_);
lean_dec(v___x_2391_);
v___x_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2392_);
return v___x_2393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg___boxed(lean_object* v_declName_2394_, lean_object* v_phase_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_){
_start:
{
uint8_t v_phase_boxed_2398_; lean_object* v_res_2399_; 
v_phase_boxed_2398_ = lean_unbox(v_phase_2395_);
v_res_2399_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_declName_2394_, v_phase_boxed_2398_, v_a_2396_);
lean_dec(v_a_2396_);
lean_dec(v_declName_2394_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f(lean_object* v_declName_2400_, uint8_t v_phase_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_declName_2400_, v_phase_2401_, v_a_2405_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___boxed(lean_object* v_declName_2408_, lean_object* v_phase_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_){
_start:
{
uint8_t v_phase_boxed_2415_; lean_object* v_res_2416_; 
v_phase_boxed_2415_ = lean_unbox(v_phase_2409_);
v_res_2416_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f(v_declName_2408_, v_phase_boxed_2415_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v_a_2413_);
lean_dec_ref(v_a_2412_);
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
lean_dec(v_declName_2408_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDecl_x3f___redArg(lean_object* v_declName_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_2418_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; uint8_t v___x_2423_; lean_object* v___x_2424_; lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2448_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_a_2422_);
lean_dec_ref_known(v___x_2421_, 1);
v___x_2423_ = lean_unbox(v_a_2422_);
v___x_2424_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_declName_2417_, v___x_2423_, v_a_2419_);
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2427_ = v___x_2424_;
v_isShared_2428_ = v_isSharedCheck_2448_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2448_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
if (lean_obj_tag(v_a_2425_) == 1)
{
lean_object* v_val_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2443_; 
v_val_2429_ = lean_ctor_get(v_a_2425_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_a_2425_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2431_ = v_a_2425_;
v_isShared_2432_ = v_isSharedCheck_2443_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_val_2429_);
lean_dec(v_a_2425_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2443_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
uint8_t v___x_2433_; uint8_t v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2438_; 
v___x_2433_ = lean_unbox(v_a_2422_);
lean_dec(v_a_2422_);
v___x_2434_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_2433_);
v___x_2435_ = lean_box(v___x_2434_);
v___x_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
lean_ctor_set(v___x_2436_, 1, v_val_2429_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 0, v___x_2436_);
v___x_2438_ = v___x_2431_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2436_);
v___x_2438_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
lean_object* v___x_2440_; 
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v___x_2438_);
v___x_2440_ = v___x_2427_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2438_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
else
{
lean_object* v___x_2444_; lean_object* v___x_2446_; 
lean_dec(v_a_2425_);
lean_dec(v_a_2422_);
v___x_2444_ = lean_box(0);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v___x_2444_);
v___x_2446_ = v___x_2427_;
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
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
v_a_2449_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2421_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2421_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDecl_x3f___redArg___boxed(lean_object* v_declName_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_Lean_Compiler_LCNF_getLocalDecl_x3f___redArg(v_declName_2457_, v_a_2458_, v_a_2459_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
lean_dec(v_declName_2457_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDecl_x3f(lean_object* v_declName_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_2463_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; uint8_t v___x_2470_; lean_object* v___x_2471_; lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2495_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_a_2469_);
lean_dec_ref_known(v___x_2468_, 1);
v___x_2470_ = lean_unbox(v_a_2469_);
v___x_2471_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_declName_2462_, v___x_2470_, v_a_2466_);
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2474_ = v___x_2471_;
v_isShared_2475_ = v_isSharedCheck_2495_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2471_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2495_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
if (lean_obj_tag(v_a_2472_) == 1)
{
lean_object* v_val_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2490_; 
v_val_2476_ = lean_ctor_get(v_a_2472_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v_a_2472_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2478_ = v_a_2472_;
v_isShared_2479_ = v_isSharedCheck_2490_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_val_2476_);
lean_dec(v_a_2472_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2490_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
uint8_t v___x_2480_; uint8_t v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2485_; 
v___x_2480_ = lean_unbox(v_a_2469_);
lean_dec(v_a_2469_);
v___x_2481_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_2480_);
v___x_2482_ = lean_box(v___x_2481_);
v___x_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
lean_ctor_set(v___x_2483_, 1, v_val_2476_);
if (v_isShared_2479_ == 0)
{
lean_ctor_set(v___x_2478_, 0, v___x_2483_);
v___x_2485_ = v___x_2478_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2483_);
v___x_2485_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2487_; 
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 0, v___x_2485_);
v___x_2487_ = v___x_2474_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2485_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
else
{
lean_object* v___x_2491_; lean_object* v___x_2493_; 
lean_dec(v_a_2472_);
lean_dec(v_a_2469_);
v___x_2491_ = lean_box(0);
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 0, v___x_2491_);
v___x_2493_ = v___x_2474_;
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
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
v_a_2496_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2468_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2468_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDecl_x3f___boxed(lean_object* v_declName_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Lean_Compiler_LCNF_getLocalDecl_x3f(v_declName_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
lean_dec(v_a_2508_);
lean_dec_ref(v_a_2507_);
lean_dec(v_a_2506_);
lean_dec_ref(v_a_2505_);
lean_dec(v_declName_2504_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2____boxed(lean_object* v_a_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2_();
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_recordFinalImpureDecl___lam__0(lean_object* v_name_2515_, lean_object* v_s_2516_){
_start:
{
lean_object* v_fst_2517_; lean_object* v_snd_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2527_; 
v_fst_2517_ = lean_ctor_get(v_s_2516_, 0);
v_snd_2518_ = lean_ctor_get(v_s_2516_, 1);
v_isSharedCheck_2527_ = !lean_is_exclusive(v_s_2516_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2520_ = v_s_2516_;
v_isShared_2521_ = v_isSharedCheck_2527_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_snd_2518_);
lean_inc(v_fst_2517_);
lean_dec(v_s_2516_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2527_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2525_; 
lean_inc(v_name_2515_);
v___x_2522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2522_, 0, v_name_2515_);
lean_ctor_set(v___x_2522_, 1, v_fst_2517_);
v___x_2523_ = l_Lean_NameSet_insert(v_snd_2518_, v_name_2515_);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 1, v___x_2523_);
lean_ctor_set(v___x_2520_, 0, v___x_2522_);
v___x_2525_ = v___x_2520_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2526_, 1, v___x_2523_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_recordFinalImpureDecl(lean_object* v_env_2528_, lean_object* v_name_2529_){
_start:
{
lean_object* v___x_2530_; lean_object* v_asyncMode_2531_; lean_object* v___f_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2530_ = l_Lean_Compiler_LCNF_declOrderExt;
v_asyncMode_2531_ = lean_ctor_get(v___x_2530_, 2);
v___f_2532_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_recordFinalImpureDecl___lam__0), 2, 1);
lean_closure_set(v___f_2532_, 0, v_name_2529_);
v___x_2533_ = lean_box(0);
v___x_2534_ = l_Lean_EnvExtension_modifyState___redArg(v___x_2530_, v_env_2528_, v___f_2532_, v_asyncMode_2531_, v___x_2533_);
return v___x_2534_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7(void){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2542_ = ((lean_object*)(l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__1));
v___x_2543_ = ((lean_object*)(l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__0));
v___x_2544_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2543_, v___x_2542_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1(lean_object* v_msg_2545_){
_start:
{
lean_object* v___f_2546_; lean_object* v___f_2547_; lean_object* v___f_2548_; lean_object* v___f_2549_; lean_object* v___f_2550_; lean_object* v___f_2551_; lean_object* v___f_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___f_2546_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__0));
v___f_2547_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__1));
v___f_2548_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__2));
v___f_2549_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__3));
v___f_2550_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__4));
v___f_2551_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__5));
v___f_2552_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__6));
v___x_2553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___f_2546_);
lean_ctor_set(v___x_2553_, 1, v___f_2547_);
v___x_2554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
lean_ctor_set(v___x_2554_, 1, v___f_2548_);
lean_ctor_set(v___x_2554_, 2, v___f_2549_);
lean_ctor_set(v___x_2554_, 3, v___f_2550_);
lean_ctor_set(v___x_2554_, 4, v___f_2551_);
v___x_2555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
lean_ctor_set(v___x_2555_, 1, v___f_2552_);
v___x_2556_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7, &l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7_once, _init_l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7);
v___x_2557_ = lean_unsigned_to_nat(0u);
v___x_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2556_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
v___x_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
v___x_2560_ = l_instInhabitedOfMonad___redArg(v___x_2555_, v___x_2559_);
v___x_2561_ = lean_panic_fn_borrowed(v___x_2560_, v_msg_2545_);
lean_dec(v___x_2560_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__5(lean_object* v_msg_2562_){
_start:
{
lean_object* v___f_2563_; lean_object* v___f_2564_; lean_object* v___f_2565_; lean_object* v___f_2566_; lean_object* v___f_2567_; lean_object* v___f_2568_; lean_object* v___f_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___f_2563_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__0));
v___f_2564_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__1));
v___f_2565_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__2));
v___f_2566_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__3));
v___f_2567_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__4));
v___f_2568_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__5));
v___f_2569_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__6));
v___x_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___f_2563_);
lean_ctor_set(v___x_2570_, 1, v___f_2564_);
v___x_2571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
lean_ctor_set(v___x_2571_, 1, v___f_2565_);
lean_ctor_set(v___x_2571_, 2, v___f_2566_);
lean_ctor_set(v___x_2571_, 3, v___f_2567_);
lean_ctor_set(v___x_2571_, 4, v___f_2568_);
v___x_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
lean_ctor_set(v___x_2572_, 1, v___f_2569_);
v___x_2573_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7, &l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7_once, _init_l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7);
v___x_2574_ = l_instInhabitedOfMonad___redArg(v___x_2572_, v___x_2573_);
v___x_2575_ = lean_panic_fn_borrowed(v___x_2574_, v_msg_2562_);
lean_dec(v___x_2574_);
return v___x_2575_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(lean_object* v_a_2576_, lean_object* v_x_2577_){
_start:
{
if (lean_obj_tag(v_x_2577_) == 0)
{
uint8_t v___x_2578_; 
v___x_2578_ = 0;
return v___x_2578_;
}
else
{
lean_object* v_key_2579_; lean_object* v_tail_2580_; uint8_t v___x_2581_; 
v_key_2579_ = lean_ctor_get(v_x_2577_, 0);
v_tail_2580_ = lean_ctor_get(v_x_2577_, 2);
v___x_2581_ = lean_name_eq(v_key_2579_, v_a_2576_);
if (v___x_2581_ == 0)
{
v_x_2577_ = v_tail_2580_;
goto _start;
}
else
{
return v___x_2581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg___boxed(lean_object* v_a_2583_, lean_object* v_x_2584_){
_start:
{
uint8_t v_res_2585_; lean_object* v_r_2586_; 
v_res_2585_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_2583_, v_x_2584_);
lean_dec(v_x_2584_);
lean_dec(v_a_2583_);
v_r_2586_ = lean_box(v_res_2585_);
return v_r_2586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8_spec__10___redArg(lean_object* v_x_2587_, lean_object* v_x_2588_){
_start:
{
if (lean_obj_tag(v_x_2588_) == 0)
{
return v_x_2587_;
}
else
{
lean_object* v_key_2589_; lean_object* v_value_2590_; lean_object* v_tail_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2617_; 
v_key_2589_ = lean_ctor_get(v_x_2588_, 0);
v_value_2590_ = lean_ctor_get(v_x_2588_, 1);
v_tail_2591_ = lean_ctor_get(v_x_2588_, 2);
v_isSharedCheck_2617_ = !lean_is_exclusive(v_x_2588_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2593_ = v_x_2588_;
v_isShared_2594_ = v_isSharedCheck_2617_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_tail_2591_);
lean_inc(v_value_2590_);
lean_inc(v_key_2589_);
lean_dec(v_x_2588_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2617_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2595_; uint64_t v___y_2597_; 
v___x_2595_ = lean_array_get_size(v_x_2587_);
if (lean_obj_tag(v_key_2589_) == 0)
{
uint64_t v___x_2615_; 
v___x_2615_ = 1723ULL;
v___y_2597_ = v___x_2615_;
goto v___jp_2596_;
}
else
{
uint64_t v_hash_2616_; 
v_hash_2616_ = lean_ctor_get_uint64(v_key_2589_, sizeof(void*)*2);
v___y_2597_ = v_hash_2616_;
goto v___jp_2596_;
}
v___jp_2596_:
{
uint64_t v___x_2598_; uint64_t v___x_2599_; uint64_t v_fold_2600_; uint64_t v___x_2601_; uint64_t v___x_2602_; uint64_t v___x_2603_; size_t v___x_2604_; size_t v___x_2605_; size_t v___x_2606_; size_t v___x_2607_; size_t v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2611_; 
v___x_2598_ = 32ULL;
v___x_2599_ = lean_uint64_shift_right(v___y_2597_, v___x_2598_);
v_fold_2600_ = lean_uint64_xor(v___y_2597_, v___x_2599_);
v___x_2601_ = 16ULL;
v___x_2602_ = lean_uint64_shift_right(v_fold_2600_, v___x_2601_);
v___x_2603_ = lean_uint64_xor(v_fold_2600_, v___x_2602_);
v___x_2604_ = lean_uint64_to_usize(v___x_2603_);
v___x_2605_ = lean_usize_of_nat(v___x_2595_);
v___x_2606_ = ((size_t)1ULL);
v___x_2607_ = lean_usize_sub(v___x_2605_, v___x_2606_);
v___x_2608_ = lean_usize_land(v___x_2604_, v___x_2607_);
v___x_2609_ = lean_array_uget_borrowed(v_x_2587_, v___x_2608_);
lean_inc(v___x_2609_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 2, v___x_2609_);
v___x_2611_ = v___x_2593_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_key_2589_);
lean_ctor_set(v_reuseFailAlloc_2614_, 1, v_value_2590_);
lean_ctor_set(v_reuseFailAlloc_2614_, 2, v___x_2609_);
v___x_2611_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
lean_object* v___x_2612_; 
v___x_2612_ = lean_array_uset(v_x_2587_, v___x_2608_, v___x_2611_);
v_x_2587_ = v___x_2612_;
v_x_2588_ = v_tail_2591_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8___redArg(lean_object* v_i_2618_, lean_object* v_source_2619_, lean_object* v_target_2620_){
_start:
{
lean_object* v___x_2621_; uint8_t v___x_2622_; 
v___x_2621_ = lean_array_get_size(v_source_2619_);
v___x_2622_ = lean_nat_dec_lt(v_i_2618_, v___x_2621_);
if (v___x_2622_ == 0)
{
lean_dec_ref(v_source_2619_);
lean_dec(v_i_2618_);
return v_target_2620_;
}
else
{
lean_object* v_es_2623_; lean_object* v___x_2624_; lean_object* v_source_2625_; lean_object* v_target_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v_es_2623_ = lean_array_fget(v_source_2619_, v_i_2618_);
v___x_2624_ = lean_box(0);
v_source_2625_ = lean_array_fset(v_source_2619_, v_i_2618_, v___x_2624_);
v_target_2626_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8_spec__10___redArg(v_target_2620_, v_es_2623_);
v___x_2627_ = lean_unsigned_to_nat(1u);
v___x_2628_ = lean_nat_add(v_i_2618_, v___x_2627_);
lean_dec(v_i_2618_);
v_i_2618_ = v___x_2628_;
v_source_2619_ = v_source_2625_;
v_target_2620_ = v_target_2626_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6___redArg(lean_object* v_data_2630_){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v_nbuckets_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2631_ = lean_array_get_size(v_data_2630_);
v___x_2632_ = lean_unsigned_to_nat(2u);
v_nbuckets_2633_ = lean_nat_mul(v___x_2631_, v___x_2632_);
v___x_2634_ = lean_unsigned_to_nat(0u);
v___x_2635_ = lean_box(0);
v___x_2636_ = lean_mk_array(v_nbuckets_2633_, v___x_2635_);
v___x_2637_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8___redArg(v___x_2634_, v_data_2630_, v___x_2636_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__0___redArg(lean_object* v_m_2638_, lean_object* v_a_2639_, lean_object* v_b_2640_){
_start:
{
lean_object* v_size_2641_; lean_object* v_buckets_2642_; lean_object* v___x_2643_; uint64_t v___y_2645_; 
v_size_2641_ = lean_ctor_get(v_m_2638_, 0);
v_buckets_2642_ = lean_ctor_get(v_m_2638_, 1);
v___x_2643_ = lean_array_get_size(v_buckets_2642_);
if (lean_obj_tag(v_a_2639_) == 0)
{
uint64_t v___x_2682_; 
v___x_2682_ = 1723ULL;
v___y_2645_ = v___x_2682_;
goto v___jp_2644_;
}
else
{
uint64_t v_hash_2683_; 
v_hash_2683_ = lean_ctor_get_uint64(v_a_2639_, sizeof(void*)*2);
v___y_2645_ = v_hash_2683_;
goto v___jp_2644_;
}
v___jp_2644_:
{
uint64_t v___x_2646_; uint64_t v___x_2647_; uint64_t v_fold_2648_; uint64_t v___x_2649_; uint64_t v___x_2650_; uint64_t v___x_2651_; size_t v___x_2652_; size_t v___x_2653_; size_t v___x_2654_; size_t v___x_2655_; size_t v___x_2656_; lean_object* v_bkt_2657_; uint8_t v___x_2658_; 
v___x_2646_ = 32ULL;
v___x_2647_ = lean_uint64_shift_right(v___y_2645_, v___x_2646_);
v_fold_2648_ = lean_uint64_xor(v___y_2645_, v___x_2647_);
v___x_2649_ = 16ULL;
v___x_2650_ = lean_uint64_shift_right(v_fold_2648_, v___x_2649_);
v___x_2651_ = lean_uint64_xor(v_fold_2648_, v___x_2650_);
v___x_2652_ = lean_uint64_to_usize(v___x_2651_);
v___x_2653_ = lean_usize_of_nat(v___x_2643_);
v___x_2654_ = ((size_t)1ULL);
v___x_2655_ = lean_usize_sub(v___x_2653_, v___x_2654_);
v___x_2656_ = lean_usize_land(v___x_2652_, v___x_2655_);
v_bkt_2657_ = lean_array_uget_borrowed(v_buckets_2642_, v___x_2656_);
v___x_2658_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_2639_, v_bkt_2657_);
if (v___x_2658_ == 0)
{
lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2679_; 
lean_inc_ref(v_buckets_2642_);
lean_inc(v_size_2641_);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_m_2638_);
if (v_isSharedCheck_2679_ == 0)
{
lean_object* v_unused_2680_; lean_object* v_unused_2681_; 
v_unused_2680_ = lean_ctor_get(v_m_2638_, 1);
lean_dec(v_unused_2680_);
v_unused_2681_ = lean_ctor_get(v_m_2638_, 0);
lean_dec(v_unused_2681_);
v___x_2660_ = v_m_2638_;
v_isShared_2661_ = v_isSharedCheck_2679_;
goto v_resetjp_2659_;
}
else
{
lean_dec(v_m_2638_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2679_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2662_; lean_object* v_size_x27_2663_; lean_object* v___x_2664_; lean_object* v_buckets_x27_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; uint8_t v___x_2671_; 
v___x_2662_ = lean_unsigned_to_nat(1u);
v_size_x27_2663_ = lean_nat_add(v_size_2641_, v___x_2662_);
lean_dec(v_size_2641_);
lean_inc(v_bkt_2657_);
v___x_2664_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2664_, 0, v_a_2639_);
lean_ctor_set(v___x_2664_, 1, v_b_2640_);
lean_ctor_set(v___x_2664_, 2, v_bkt_2657_);
v_buckets_x27_2665_ = lean_array_uset(v_buckets_2642_, v___x_2656_, v___x_2664_);
v___x_2666_ = lean_unsigned_to_nat(4u);
v___x_2667_ = lean_nat_mul(v_size_x27_2663_, v___x_2666_);
v___x_2668_ = lean_unsigned_to_nat(3u);
v___x_2669_ = lean_nat_div(v___x_2667_, v___x_2668_);
lean_dec(v___x_2667_);
v___x_2670_ = lean_array_get_size(v_buckets_x27_2665_);
v___x_2671_ = lean_nat_dec_le(v___x_2669_, v___x_2670_);
lean_dec(v___x_2669_);
if (v___x_2671_ == 0)
{
lean_object* v_val_2672_; lean_object* v___x_2674_; 
v_val_2672_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6___redArg(v_buckets_x27_2665_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 1, v_val_2672_);
lean_ctor_set(v___x_2660_, 0, v_size_x27_2663_);
v___x_2674_ = v___x_2660_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_size_x27_2663_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v_val_2672_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
else
{
lean_object* v___x_2677_; 
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 1, v_buckets_x27_2665_);
lean_ctor_set(v___x_2660_, 0, v_size_x27_2663_);
v___x_2677_ = v___x_2660_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_size_x27_2663_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v_buckets_x27_2665_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
else
{
lean_dec(v_b_2640_);
lean_dec(v_a_2639_);
return v_m_2638_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__1(lean_object* v_as_2684_, size_t v_sz_2685_, size_t v_i_2686_, lean_object* v_b_2687_){
_start:
{
uint8_t v___x_2688_; 
v___x_2688_ = lean_usize_dec_lt(v_i_2686_, v_sz_2685_);
if (v___x_2688_ == 0)
{
return v_b_2687_;
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2690_; lean_object* v_r_2691_; size_t v___x_2692_; size_t v___x_2693_; 
v_a_2689_ = lean_array_uget_borrowed(v_as_2684_, v_i_2686_);
v___x_2690_ = lean_box(0);
lean_inc(v_a_2689_);
v_r_2691_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__0___redArg(v_b_2687_, v_a_2689_, v___x_2690_);
v___x_2692_ = ((size_t)1ULL);
v___x_2693_ = lean_usize_add(v_i_2686_, v___x_2692_);
v_i_2686_ = v___x_2693_;
v_b_2687_ = v_r_2691_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__1___boxed(lean_object* v_as_2695_, lean_object* v_sz_2696_, lean_object* v_i_2697_, lean_object* v_b_2698_){
_start:
{
size_t v_sz_boxed_2699_; size_t v_i_boxed_2700_; lean_object* v_res_2701_; 
v_sz_boxed_2699_ = lean_unbox_usize(v_sz_2696_);
lean_dec(v_sz_2696_);
v_i_boxed_2700_ = lean_unbox_usize(v_i_2697_);
lean_dec(v_i_2697_);
v_res_2701_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__1(v_as_2695_, v_sz_boxed_2699_, v_i_boxed_2700_, v_b_2698_);
lean_dec_ref(v_as_2695_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0(lean_object* v_m_2702_, lean_object* v_l_2703_){
_start:
{
size_t v_sz_2704_; size_t v___x_2705_; lean_object* v___x_2706_; 
v_sz_2704_ = lean_array_size(v_l_2703_);
v___x_2705_ = ((size_t)0ULL);
v___x_2706_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__1(v_l_2703_, v_sz_2704_, v___x_2705_, v_m_2702_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0___boxed(lean_object* v_m_2707_, lean_object* v_l_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0(v_m_2707_, v_l_2708_);
lean_dec_ref(v_l_2708_);
return v_res_2709_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg(lean_object* v_m_2710_, lean_object* v_a_2711_){
_start:
{
lean_object* v_buckets_2712_; lean_object* v___x_2713_; uint64_t v___y_2715_; 
v_buckets_2712_ = lean_ctor_get(v_m_2710_, 1);
v___x_2713_ = lean_array_get_size(v_buckets_2712_);
if (lean_obj_tag(v_a_2711_) == 0)
{
uint64_t v___x_2729_; 
v___x_2729_ = 1723ULL;
v___y_2715_ = v___x_2729_;
goto v___jp_2714_;
}
else
{
uint64_t v_hash_2730_; 
v_hash_2730_ = lean_ctor_get_uint64(v_a_2711_, sizeof(void*)*2);
v___y_2715_ = v_hash_2730_;
goto v___jp_2714_;
}
v___jp_2714_:
{
uint64_t v___x_2716_; uint64_t v___x_2717_; uint64_t v_fold_2718_; uint64_t v___x_2719_; uint64_t v___x_2720_; uint64_t v___x_2721_; size_t v___x_2722_; size_t v___x_2723_; size_t v___x_2724_; size_t v___x_2725_; size_t v___x_2726_; lean_object* v___x_2727_; uint8_t v___x_2728_; 
v___x_2716_ = 32ULL;
v___x_2717_ = lean_uint64_shift_right(v___y_2715_, v___x_2716_);
v_fold_2718_ = lean_uint64_xor(v___y_2715_, v___x_2717_);
v___x_2719_ = 16ULL;
v___x_2720_ = lean_uint64_shift_right(v_fold_2718_, v___x_2719_);
v___x_2721_ = lean_uint64_xor(v_fold_2718_, v___x_2720_);
v___x_2722_ = lean_uint64_to_usize(v___x_2721_);
v___x_2723_ = lean_usize_of_nat(v___x_2713_);
v___x_2724_ = ((size_t)1ULL);
v___x_2725_ = lean_usize_sub(v___x_2723_, v___x_2724_);
v___x_2726_ = lean_usize_land(v___x_2722_, v___x_2725_);
v___x_2727_ = lean_array_uget_borrowed(v_buckets_2712_, v___x_2726_);
v___x_2728_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_2711_, v___x_2727_);
return v___x_2728_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg___boxed(lean_object* v_m_2731_, lean_object* v_a_2732_){
_start:
{
uint8_t v_res_2733_; lean_object* v_r_2734_; 
v_res_2733_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg(v_m_2731_, v_a_2732_);
lean_dec(v_a_2732_);
lean_dec_ref(v_m_2731_);
v_r_2734_ = lean_box(v_res_2733_);
return v_r_2734_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7___redArg(lean_object* v_a_2735_, lean_object* v_b_2736_, lean_object* v_x_2737_){
_start:
{
if (lean_obj_tag(v_x_2737_) == 0)
{
lean_dec(v_b_2736_);
lean_dec(v_a_2735_);
return v_x_2737_;
}
else
{
lean_object* v_key_2738_; lean_object* v_value_2739_; lean_object* v_tail_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2752_; 
v_key_2738_ = lean_ctor_get(v_x_2737_, 0);
v_value_2739_ = lean_ctor_get(v_x_2737_, 1);
v_tail_2740_ = lean_ctor_get(v_x_2737_, 2);
v_isSharedCheck_2752_ = !lean_is_exclusive(v_x_2737_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2742_ = v_x_2737_;
v_isShared_2743_ = v_isSharedCheck_2752_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_tail_2740_);
lean_inc(v_value_2739_);
lean_inc(v_key_2738_);
lean_dec(v_x_2737_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2752_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
uint8_t v___x_2744_; 
v___x_2744_ = lean_name_eq(v_key_2738_, v_a_2735_);
if (v___x_2744_ == 0)
{
lean_object* v___x_2745_; lean_object* v___x_2747_; 
v___x_2745_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7___redArg(v_a_2735_, v_b_2736_, v_tail_2740_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 2, v___x_2745_);
v___x_2747_ = v___x_2742_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_key_2738_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v_value_2739_);
lean_ctor_set(v_reuseFailAlloc_2748_, 2, v___x_2745_);
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
lean_dec(v_value_2739_);
lean_dec(v_key_2738_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 1, v_b_2736_);
lean_ctor_set(v___x_2742_, 0, v_a_2735_);
v___x_2750_ = v___x_2742_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2735_);
lean_ctor_set(v_reuseFailAlloc_2751_, 1, v_b_2736_);
lean_ctor_set(v_reuseFailAlloc_2751_, 2, v_tail_2740_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3___redArg(lean_object* v_m_2753_, lean_object* v_a_2754_, lean_object* v_b_2755_){
_start:
{
lean_object* v_size_2756_; lean_object* v_buckets_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2803_; 
v_size_2756_ = lean_ctor_get(v_m_2753_, 0);
v_buckets_2757_ = lean_ctor_get(v_m_2753_, 1);
v_isSharedCheck_2803_ = !lean_is_exclusive(v_m_2753_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2759_ = v_m_2753_;
v_isShared_2760_ = v_isSharedCheck_2803_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_buckets_2757_);
lean_inc(v_size_2756_);
lean_dec(v_m_2753_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2803_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2761_; uint64_t v___y_2763_; 
v___x_2761_ = lean_array_get_size(v_buckets_2757_);
if (lean_obj_tag(v_a_2754_) == 0)
{
uint64_t v___x_2801_; 
v___x_2801_ = 1723ULL;
v___y_2763_ = v___x_2801_;
goto v___jp_2762_;
}
else
{
uint64_t v_hash_2802_; 
v_hash_2802_ = lean_ctor_get_uint64(v_a_2754_, sizeof(void*)*2);
v___y_2763_ = v_hash_2802_;
goto v___jp_2762_;
}
v___jp_2762_:
{
uint64_t v___x_2764_; uint64_t v___x_2765_; uint64_t v_fold_2766_; uint64_t v___x_2767_; uint64_t v___x_2768_; uint64_t v___x_2769_; size_t v___x_2770_; size_t v___x_2771_; size_t v___x_2772_; size_t v___x_2773_; size_t v___x_2774_; lean_object* v_bkt_2775_; uint8_t v___x_2776_; 
v___x_2764_ = 32ULL;
v___x_2765_ = lean_uint64_shift_right(v___y_2763_, v___x_2764_);
v_fold_2766_ = lean_uint64_xor(v___y_2763_, v___x_2765_);
v___x_2767_ = 16ULL;
v___x_2768_ = lean_uint64_shift_right(v_fold_2766_, v___x_2767_);
v___x_2769_ = lean_uint64_xor(v_fold_2766_, v___x_2768_);
v___x_2770_ = lean_uint64_to_usize(v___x_2769_);
v___x_2771_ = lean_usize_of_nat(v___x_2761_);
v___x_2772_ = ((size_t)1ULL);
v___x_2773_ = lean_usize_sub(v___x_2771_, v___x_2772_);
v___x_2774_ = lean_usize_land(v___x_2770_, v___x_2773_);
v_bkt_2775_ = lean_array_uget_borrowed(v_buckets_2757_, v___x_2774_);
v___x_2776_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_2754_, v_bkt_2775_);
if (v___x_2776_ == 0)
{
lean_object* v___x_2777_; lean_object* v_size_x27_2778_; lean_object* v___x_2779_; lean_object* v_buckets_x27_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; uint8_t v___x_2786_; 
v___x_2777_ = lean_unsigned_to_nat(1u);
v_size_x27_2778_ = lean_nat_add(v_size_2756_, v___x_2777_);
lean_dec(v_size_2756_);
lean_inc(v_bkt_2775_);
v___x_2779_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2779_, 0, v_a_2754_);
lean_ctor_set(v___x_2779_, 1, v_b_2755_);
lean_ctor_set(v___x_2779_, 2, v_bkt_2775_);
v_buckets_x27_2780_ = lean_array_uset(v_buckets_2757_, v___x_2774_, v___x_2779_);
v___x_2781_ = lean_unsigned_to_nat(4u);
v___x_2782_ = lean_nat_mul(v_size_x27_2778_, v___x_2781_);
v___x_2783_ = lean_unsigned_to_nat(3u);
v___x_2784_ = lean_nat_div(v___x_2782_, v___x_2783_);
lean_dec(v___x_2782_);
v___x_2785_ = lean_array_get_size(v_buckets_x27_2780_);
v___x_2786_ = lean_nat_dec_le(v___x_2784_, v___x_2785_);
lean_dec(v___x_2784_);
if (v___x_2786_ == 0)
{
lean_object* v_val_2787_; lean_object* v___x_2789_; 
v_val_2787_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6___redArg(v_buckets_x27_2780_);
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 1, v_val_2787_);
lean_ctor_set(v___x_2759_, 0, v_size_x27_2778_);
v___x_2789_ = v___x_2759_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_size_x27_2778_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v_val_2787_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
else
{
lean_object* v___x_2792_; 
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 1, v_buckets_x27_2780_);
lean_ctor_set(v___x_2759_, 0, v_size_x27_2778_);
v___x_2792_ = v___x_2759_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_size_x27_2778_);
lean_ctor_set(v_reuseFailAlloc_2793_, 1, v_buckets_x27_2780_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
else
{
lean_object* v___x_2794_; lean_object* v_buckets_x27_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2799_; 
lean_inc(v_bkt_2775_);
v___x_2794_ = lean_box(0);
v_buckets_x27_2795_ = lean_array_uset(v_buckets_2757_, v___x_2774_, v___x_2794_);
v___x_2796_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7___redArg(v_a_2754_, v_b_2755_, v_bkt_2775_);
v___x_2797_ = lean_array_uset(v_buckets_x27_2795_, v___x_2774_, v___x_2796_);
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 1, v___x_2797_);
v___x_2799_ = v___x_2759_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_size_2756_);
lean_ctor_set(v_reuseFailAlloc_2800_, 1, v___x_2797_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2807_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__2));
v___x_2808_ = lean_unsigned_to_nat(4u);
v___x_2809_ = lean_unsigned_to_nat(238u);
v___x_2810_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__1));
v___x_2811_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__0));
v___x_2812_ = l_mkPanicMessageWithDecl(v___x_2811_, v___x_2810_, v___x_2809_, v___x_2808_, v___x_2807_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg(lean_object* v___x_2813_, lean_object* v_as_x27_2814_, lean_object* v_b_2815_){
_start:
{
if (lean_obj_tag(v_as_x27_2814_) == 0)
{
return v_b_2815_;
}
else
{
lean_object* v_head_2816_; lean_object* v_tail_2817_; lean_object* v_fst_2818_; lean_object* v_snd_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2840_; 
v_head_2816_ = lean_ctor_get(v_as_x27_2814_, 0);
v_tail_2817_ = lean_ctor_get(v_as_x27_2814_, 1);
v_fst_2818_ = lean_ctor_get(v_b_2815_, 0);
v_snd_2819_ = lean_ctor_get(v_b_2815_, 1);
v_isSharedCheck_2840_ = !lean_is_exclusive(v_b_2815_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2821_ = v_b_2815_;
v_isShared_2822_ = v_isSharedCheck_2840_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_snd_2819_);
lean_inc(v_fst_2818_);
lean_dec(v_b_2815_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2840_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v_map_2824_; uint8_t v___x_2838_; 
v___x_2838_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg(v___x_2813_, v_head_2816_);
if (v___x_2838_ == 0)
{
v_map_2824_ = v_fst_2818_;
goto v___jp_2823_;
}
else
{
lean_object* v___x_2839_; 
lean_inc(v_snd_2819_);
lean_inc(v_head_2816_);
v___x_2839_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3___redArg(v_fst_2818_, v_head_2816_, v_snd_2819_);
v_map_2824_ = v___x_2839_;
goto v___jp_2823_;
}
v___jp_2823_:
{
lean_object* v___x_2825_; uint8_t v___x_2826_; 
v___x_2825_ = lean_unsigned_to_nat(0u);
v___x_2826_ = lean_nat_dec_eq(v_snd_2819_, v___x_2825_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2830_; 
v___x_2827_ = lean_unsigned_to_nat(1u);
v___x_2828_ = lean_nat_sub(v_snd_2819_, v___x_2827_);
lean_dec(v_snd_2819_);
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 1, v___x_2828_);
lean_ctor_set(v___x_2821_, 0, v_map_2824_);
v___x_2830_ = v___x_2821_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_map_2824_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v___x_2828_);
v___x_2830_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
v_as_x27_2814_ = v_tail_2817_;
v_b_2815_ = v___x_2830_;
goto _start;
}
}
else
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
lean_dec_ref(v_map_2824_);
lean_del_object(v___x_2821_);
lean_dec(v_snd_2819_);
v___x_2833_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3);
v___x_2834_ = l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1(v___x_2833_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2835_);
lean_dec_ref_known(v___x_2834_, 1);
return v_a_2835_;
}
else
{
lean_object* v_a_2836_; 
v_a_2836_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2836_);
lean_dec_ref_known(v___x_2834_, 1);
v_as_x27_2814_ = v_tail_2817_;
v_b_2815_ = v_a_2836_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___boxed(lean_object* v___x_2841_, lean_object* v_as_x27_2842_, lean_object* v_b_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg(v___x_2841_, v_as_x27_2842_, v_b_2843_);
lean_dec(v_as_x27_2842_);
lean_dec_ref(v___x_2841_);
return v_res_2844_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0(void){
_start:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2845_ = lean_box(0);
v___x_2846_ = lean_unsigned_to_nat(16u);
v___x_2847_ = lean_mk_array(v___x_2846_, v___x_2845_);
return v___x_2847_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1(void){
_start:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2848_ = lean_obj_once(&l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0, &l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0_once, _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0);
v___x_2849_ = lean_unsigned_to_nat(0u);
v___x_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
lean_ctor_set(v___x_2850_, 1, v___x_2848_);
return v___x_2850_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3(void){
_start:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2852_ = ((lean_object*)(l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__2));
v___x_2853_ = lean_unsigned_to_nat(2u);
v___x_2854_ = lean_unsigned_to_nat(240u);
v___x_2855_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__1));
v___x_2856_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__0));
v___x_2857_ = l_mkPanicMessageWithDecl(v___x_2856_, v___x_2855_, v___x_2854_, v___x_2853_, v___x_2852_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureDeclIndices(lean_object* v_env_2858_, lean_object* v_targets_2859_){
_start:
{
lean_object* v___x_2860_; lean_object* v_asyncMode_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v_fst_2865_; lean_object* v_snd_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2895_; 
v___x_2860_ = l_Lean_Compiler_LCNF_declOrderExt;
v_asyncMode_2861_ = lean_ctor_get(v___x_2860_, 2);
v___x_2862_ = ((lean_object*)(l_Lean_Compiler_LCNF_isDeclTransparent___closed__0));
v___x_2863_ = lean_box(0);
v___x_2864_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2862_, v___x_2860_, v_env_2858_, v_asyncMode_2861_, v___x_2863_);
v_fst_2865_ = lean_ctor_get(v___x_2864_, 0);
v_snd_2866_ = lean_ctor_get(v___x_2864_, 1);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2868_ = v___x_2864_;
v_isShared_2869_ = v_isSharedCheck_2895_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_snd_2866_);
lean_inc(v_fst_2865_);
lean_dec(v___x_2864_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2895_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___y_2871_; 
if (lean_obj_tag(v_snd_2866_) == 0)
{
lean_object* v_size_2893_; 
v_size_2893_ = lean_ctor_get(v_snd_2866_, 0);
lean_inc(v_size_2893_);
lean_dec_ref_known(v_snd_2866_, 5);
v___y_2871_ = v_size_2893_;
goto v___jp_2870_;
}
else
{
lean_object* v___x_2894_; 
v___x_2894_ = lean_unsigned_to_nat(0u);
v___y_2871_ = v___x_2894_;
goto v___jp_2870_;
}
v___jp_2870_:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v_map_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2884_; 
v___x_2872_ = lean_unsigned_to_nat(0u);
v___x_2873_ = lean_unsigned_to_nat(4u);
v___x_2874_ = lean_nat_mul(v___y_2871_, v___x_2873_);
v___x_2875_ = lean_unsigned_to_nat(3u);
v___x_2876_ = lean_nat_div(v___x_2874_, v___x_2875_);
lean_dec(v___x_2874_);
v___x_2877_ = l_Nat_nextPowerOfTwo(v___x_2876_);
lean_dec(v___x_2876_);
v___x_2878_ = lean_box(0);
v___x_2879_ = lean_mk_array(v___x_2877_, v___x_2878_);
v_map_2880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_map_2880_, 0, v___x_2872_);
lean_ctor_set(v_map_2880_, 1, v___x_2879_);
v___x_2881_ = lean_obj_once(&l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1, &l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1_once, _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1);
v___x_2882_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0(v___x_2881_, v_targets_2859_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 1, v___y_2871_);
lean_ctor_set(v___x_2868_, 0, v_map_2880_);
v___x_2884_ = v___x_2868_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_map_2880_);
lean_ctor_set(v_reuseFailAlloc_2892_, 1, v___y_2871_);
v___x_2884_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
lean_object* v___x_2885_; lean_object* v_fst_2886_; lean_object* v_size_2887_; lean_object* v___x_2888_; uint8_t v___x_2889_; 
v___x_2885_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg(v___x_2882_, v_fst_2865_, v___x_2884_);
lean_dec(v_fst_2865_);
lean_dec_ref(v___x_2882_);
v_fst_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_fst_2886_);
lean_dec_ref(v___x_2885_);
v_size_2887_ = lean_ctor_get(v_fst_2886_, 0);
v___x_2888_ = lean_array_get_size(v_targets_2859_);
v___x_2889_ = lean_nat_dec_eq(v_size_2887_, v___x_2888_);
if (v___x_2889_ == 0)
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
lean_dec(v_fst_2886_);
v___x_2890_ = lean_obj_once(&l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3, &l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3_once, _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3);
v___x_2891_ = l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__5(v___x_2890_);
return v___x_2891_;
}
else
{
return v_fst_2886_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureDeclIndices___boxed(lean_object* v_env_2896_, lean_object* v_targets_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l_Lean_Compiler_LCNF_getImpureDeclIndices(v_env_2896_, v_targets_2897_);
lean_dec_ref(v_targets_2897_);
return v_res_2898_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2(lean_object* v_00_u03b2_2899_, lean_object* v_m_2900_, lean_object* v_a_2901_){
_start:
{
uint8_t v___x_2902_; 
v___x_2902_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg(v_m_2900_, v_a_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___boxed(lean_object* v_00_u03b2_2903_, lean_object* v_m_2904_, lean_object* v_a_2905_){
_start:
{
uint8_t v_res_2906_; lean_object* v_r_2907_; 
v_res_2906_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2(v_00_u03b2_2903_, v_m_2904_, v_a_2905_);
lean_dec(v_a_2905_);
lean_dec_ref(v_m_2904_);
v_r_2907_ = lean_box(v_res_2906_);
return v_r_2907_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3(lean_object* v_00_u03b2_2908_, lean_object* v_m_2909_, lean_object* v_a_2910_, lean_object* v_b_2911_){
_start:
{
lean_object* v___x_2912_; 
v___x_2912_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3___redArg(v_m_2909_, v_a_2910_, v_b_2911_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4(lean_object* v___x_2913_, lean_object* v_as_2914_, lean_object* v_as_x27_2915_, lean_object* v_b_2916_, lean_object* v_a_2917_){
_start:
{
lean_object* v___x_2918_; 
v___x_2918_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg(v___x_2913_, v_as_x27_2915_, v_b_2916_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___boxed(lean_object* v___x_2919_, lean_object* v_as_2920_, lean_object* v_as_x27_2921_, lean_object* v_b_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4(v___x_2919_, v_as_2920_, v_as_x27_2921_, v_b_2922_, v_a_2923_);
lean_dec(v_as_x27_2921_);
lean_dec(v_as_2920_);
lean_dec_ref(v___x_2919_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__0(lean_object* v_00_u03b2_2925_, lean_object* v_m_2926_, lean_object* v_a_2927_, lean_object* v_b_2928_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__0___redArg(v_m_2926_, v_a_2927_, v_b_2928_);
return v___x_2929_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4(lean_object* v_00_u03b2_2930_, lean_object* v_a_2931_, lean_object* v_x_2932_){
_start:
{
uint8_t v___x_2933_; 
v___x_2933_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_2931_, v_x_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2934_, lean_object* v_a_2935_, lean_object* v_x_2936_){
_start:
{
uint8_t v_res_2937_; lean_object* v_r_2938_; 
v_res_2937_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4(v_00_u03b2_2934_, v_a_2935_, v_x_2936_);
lean_dec(v_x_2936_);
lean_dec(v_a_2935_);
v_r_2938_ = lean_box(v_res_2937_);
return v_r_2938_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6(lean_object* v_00_u03b2_2939_, lean_object* v_data_2940_){
_start:
{
lean_object* v___x_2941_; 
v___x_2941_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6___redArg(v_data_2940_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7(lean_object* v_00_u03b2_2942_, lean_object* v_a_2943_, lean_object* v_b_2944_, lean_object* v_x_2945_){
_start:
{
lean_object* v___x_2946_; 
v___x_2946_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7___redArg(v_a_2943_, v_b_2944_, v_x_2945_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_2947_, lean_object* v_i_2948_, lean_object* v_source_2949_, lean_object* v_target_2950_){
_start:
{
lean_object* v___x_2951_; 
v___x_2951_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8___redArg(v_i_2948_, v_source_2949_, v_target_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_2952_, lean_object* v_x_2953_, lean_object* v_x_2954_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8_spec__10___redArg(v_x_2953_, v_x_2954_);
return v___x_2955_;
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
