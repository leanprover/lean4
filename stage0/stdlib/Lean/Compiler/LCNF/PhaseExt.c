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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instDecidableEqOLeanLevel(uint8_t, uint8_t);
uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
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
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_instInhabitedPersistentEnvExtension(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0;
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
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__3;
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
static const lean_array_object l_Lean_Compiler_LCNF_mkDeclExt___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__1___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___lam__1___closed__0_value;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "baseExt"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(145, 223, 165, 126, 7, 177, 183, 38)}};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_baseExt;
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "monoExt"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 71, 195, 20, 53, 75, 103, 187)}};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_monoExt;
static const lean_closure_object l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___boxed, .m_arity = 6, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_impureExt;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedSigExt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedSigExt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___closed__1;
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
static const lean_array_object l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Compiler_LCNF_mkSigDeclExt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__2_value)} };
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
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "impureSigExt"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(245, 150, 154, 56, 193, 204, 147, 237)}};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_impureSigExt;
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(lean_object* v_lt_157_, lean_object* v_as_158_, lean_object* v_lo_159_, lean_object* v_hi_160_){
_start:
{
uint8_t v___x_161_; 
v___x_161_ = lean_nat_dec_lt(v_lo_159_, v_hi_160_);
if (v___x_161_ == 0)
{
lean_dec(v_lo_159_);
lean_dec_ref(v_lt_157_);
return v_as_158_;
}
else
{
lean_object* v___x_162_; lean_object* v_fst_163_; lean_object* v_snd_164_; uint8_t v___x_165_; 
lean_inc(v_lo_159_);
lean_inc_ref(v_lt_157_);
v___x_162_ = l_Array_qpartition___redArg(v_as_158_, v_lt_157_, v_lo_159_, v_hi_160_);
v_fst_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_fst_163_);
v_snd_164_ = lean_ctor_get(v___x_162_, 1);
lean_inc(v_snd_164_);
lean_dec_ref(v___x_162_);
v___x_165_ = lean_nat_dec_le(v_hi_160_, v_fst_163_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
lean_inc_ref(v_lt_157_);
v___x_166_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_157_, v_snd_164_, v_lo_159_, v_fst_163_);
v___x_167_ = lean_unsigned_to_nat(1u);
v___x_168_ = lean_nat_add(v_fst_163_, v___x_167_);
lean_dec(v_fst_163_);
v_as_158_ = v___x_166_;
v_lo_159_ = v___x_168_;
goto _start;
}
else
{
lean_dec(v_fst_163_);
lean_dec(v_lo_159_);
lean_dec_ref(v_lt_157_);
return v_snd_164_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg___boxed(lean_object* v_lt_170_, lean_object* v_as_171_, lean_object* v_lo_172_, lean_object* v_hi_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_170_, v_as_171_, v_lo_172_, v_hi_173_);
lean_dec(v_hi_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(lean_object* v_s_178_, lean_object* v_lt_179_){
_start:
{
lean_object* v___f_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v_decls_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v___f_180_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__0));
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_182_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__1));
v_decls_183_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_s_178_, v___f_180_, v___x_182_);
v___x_184_ = lean_array_get_size(v_decls_183_);
v___x_185_ = lean_nat_dec_eq(v___x_184_, v___x_181_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___y_189_; uint8_t v___x_193_; 
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = lean_nat_sub(v___x_184_, v___x_186_);
v___x_193_ = lean_nat_dec_le(v___x_181_, v___x_187_);
if (v___x_193_ == 0)
{
lean_inc(v___x_187_);
v___y_189_ = v___x_187_;
goto v___jp_188_;
}
else
{
v___y_189_ = v___x_181_;
goto v___jp_188_;
}
v___jp_188_:
{
uint8_t v___x_190_; 
v___x_190_ = lean_nat_dec_le(v___y_189_, v___x_187_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; 
lean_dec(v___x_187_);
lean_inc(v___y_189_);
v___x_191_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_179_, v_decls_183_, v___y_189_, v___y_189_);
lean_dec(v___y_189_);
return v___x_191_;
}
else
{
lean_object* v___x_192_; 
v___x_192_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_179_, v_decls_183_, v___y_189_, v___x_187_);
lean_dec(v___x_187_);
return v___x_192_;
}
}
}
else
{
lean_dec_ref(v_lt_179_);
return v_decls_183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___boxed(lean_object* v_s_194_, lean_object* v_lt_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(v_s_194_, v_lt_195_);
lean_dec_ref(v_s_194_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries(uint8_t v_pu_197_, lean_object* v_00_u03b2_198_, lean_object* v_s_199_, lean_object* v_lt_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(v_s_199_, v_lt_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___boxed(lean_object* v_pu_202_, lean_object* v_00_u03b2_203_, lean_object* v_s_204_, lean_object* v_lt_205_){
_start:
{
uint8_t v_pu_boxed_206_; lean_object* v_res_207_; 
v_pu_boxed_206_ = lean_unbox(v_pu_202_);
v_res_207_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries(v_pu_boxed_206_, v_00_u03b2_203_, v_s_204_, v_lt_205_);
lean_dec_ref(v_s_204_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0(lean_object* v_00_u03c3_208_, lean_object* v_00_u03b2_209_, lean_object* v_map_210_, lean_object* v_f_211_, lean_object* v_init_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_map_210_, v_f_211_, v_init_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___boxed(lean_object* v_00_u03c3_214_, lean_object* v_00_u03b2_215_, lean_object* v_map_216_, lean_object* v_f_217_, lean_object* v_init_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0(v_00_u03c3_214_, v_00_u03b2_215_, v_map_216_, v_f_217_, v_init_218_);
lean_dec_ref(v_map_216_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1(lean_object* v_00_u03b2_220_, lean_object* v_lt_221_, lean_object* v_n_222_, lean_object* v_as_223_, lean_object* v_lo_224_, lean_object* v_hi_225_, lean_object* v_w_226_, lean_object* v_hlo_227_, lean_object* v_hhi_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_221_, v_as_223_, v_lo_224_, v_hi_225_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___boxed(lean_object* v_00_u03b2_230_, lean_object* v_lt_231_, lean_object* v_n_232_, lean_object* v_as_233_, lean_object* v_lo_234_, lean_object* v_hi_235_, lean_object* v_w_236_, lean_object* v_hlo_237_, lean_object* v_hhi_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1(v_00_u03b2_230_, v_lt_231_, v_n_232_, v_as_233_, v_lo_234_, v_hi_235_, v_w_236_, v_hlo_237_, v_hhi_238_);
lean_dec(v_hi_235_);
lean_dec(v_n_232_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___redArg(lean_object* v_map_240_, lean_object* v_f_241_, lean_object* v_init_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v_f_241_, v_map_240_, v_init_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___redArg___boxed(lean_object* v_map_244_, lean_object* v_f_245_, lean_object* v_init_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___redArg(v_map_244_, v_f_245_, v_init_246_);
lean_dec_ref(v_map_244_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0(lean_object* v_00_u03c3_248_, lean_object* v_00_u03b2_249_, lean_object* v_map_250_, lean_object* v_f_251_, lean_object* v_init_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v_f_251_, v_map_250_, v_init_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___boxed(lean_object* v_00_u03c3_254_, lean_object* v_00_u03b2_255_, lean_object* v_map_256_, lean_object* v_f_257_, lean_object* v_init_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0(v_00_u03c3_254_, v_00_u03b2_255_, v_map_256_, v_f_257_, v_init_258_);
lean_dec_ref(v_map_256_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_260_, lean_object* v_00_u03b1_261_, lean_object* v_00_u03b2_262_, lean_object* v_f_263_, lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v_f_263_, v_x_264_, v_x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_267_, lean_object* v_00_u03b1_268_, lean_object* v_00_u03b2_269_, lean_object* v_f_270_, lean_object* v_x_271_, lean_object* v_x_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1(v_00_u03c3_267_, v_00_u03b1_268_, v_00_u03b2_269_, v_f_270_, v_x_271_, v_x_272_);
lean_dec_ref(v_x_271_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_274_, lean_object* v_00_u03b2_275_, lean_object* v_00_u03c3_276_, lean_object* v_f_277_, lean_object* v_as_278_, size_t v_i_279_, size_t v_stop_280_, lean_object* v_b_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg(v_f_277_, v_as_278_, v_i_279_, v_stop_280_, v_b_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_283_, lean_object* v_00_u03b2_284_, lean_object* v_00_u03c3_285_, lean_object* v_f_286_, lean_object* v_as_287_, lean_object* v_i_288_, lean_object* v_stop_289_, lean_object* v_b_290_){
_start:
{
size_t v_i_boxed_291_; size_t v_stop_boxed_292_; lean_object* v_res_293_; 
v_i_boxed_291_ = lean_unbox_usize(v_i_288_);
lean_dec(v_i_288_);
v_stop_boxed_292_ = lean_unbox_usize(v_stop_289_);
lean_dec(v_stop_289_);
v_res_293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_283_, v_00_u03b2_284_, v_00_u03c3_285_, v_f_286_, v_as_287_, v_i_boxed_291_, v_stop_boxed_292_, v_b_290_);
lean_dec_ref(v_as_287_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03c3_294_, lean_object* v_00_u03b1_295_, lean_object* v_00_u03b2_296_, lean_object* v_f_297_, lean_object* v_keys_298_, lean_object* v_vals_299_, lean_object* v_heq_300_, lean_object* v_i_301_, lean_object* v_acc_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___redArg(v_f_297_, v_keys_298_, v_vals_299_, v_i_301_, v_acc_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03c3_304_, lean_object* v_00_u03b1_305_, lean_object* v_00_u03b2_306_, lean_object* v_f_307_, lean_object* v_keys_308_, lean_object* v_vals_309_, lean_object* v_heq_310_, lean_object* v_i_311_, lean_object* v_acc_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4(v_00_u03c3_304_, v_00_u03b1_305_, v_00_u03b2_306_, v_f_307_, v_keys_308_, v_vals_309_, v_heq_310_, v_i_311_, v_acc_312_);
lean_dec_ref(v_vals_309_);
lean_dec_ref(v_keys_308_);
return v_res_313_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_314_, lean_object* v_i_315_, lean_object* v_k_316_){
_start:
{
lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = lean_array_get_size(v_keys_314_);
v___x_318_ = lean_nat_dec_lt(v_i_315_, v___x_317_);
if (v___x_318_ == 0)
{
lean_dec(v_i_315_);
return v___x_318_;
}
else
{
lean_object* v_k_x27_319_; uint8_t v___x_320_; 
v_k_x27_319_ = lean_array_fget_borrowed(v_keys_314_, v_i_315_);
v___x_320_ = lean_name_eq(v_k_316_, v_k_x27_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_unsigned_to_nat(1u);
v___x_322_ = lean_nat_add(v_i_315_, v___x_321_);
lean_dec(v_i_315_);
v_i_315_ = v___x_322_;
goto _start;
}
else
{
lean_dec(v_i_315_);
return v___x_320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_324_, lean_object* v_i_325_, lean_object* v_k_326_){
_start:
{
uint8_t v_res_327_; lean_object* v_r_328_; 
v_res_327_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg(v_keys_324_, v_i_325_, v_k_326_);
lean_dec(v_k_326_);
lean_dec_ref(v_keys_324_);
v_r_328_ = lean_box(v_res_327_);
return v_r_328_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_329_; size_t v___x_330_; size_t v___x_331_; 
v___x_329_ = ((size_t)5ULL);
v___x_330_ = ((size_t)1ULL);
v___x_331_ = lean_usize_shift_left(v___x_330_, v___x_329_);
return v___x_331_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_332_; size_t v___x_333_; size_t v___x_334_; 
v___x_332_ = ((size_t)1ULL);
v___x_333_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__0);
v___x_334_ = lean_usize_sub(v___x_333_, v___x_332_);
return v___x_334_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg(lean_object* v_x_335_, size_t v_x_336_, lean_object* v_x_337_){
_start:
{
if (lean_obj_tag(v_x_335_) == 0)
{
lean_object* v_es_338_; lean_object* v___x_339_; size_t v___x_340_; size_t v___x_341_; size_t v___x_342_; lean_object* v_j_343_; lean_object* v___x_344_; 
v_es_338_ = lean_ctor_get(v_x_335_, 0);
lean_inc_ref(v_es_338_);
lean_dec_ref(v_x_335_);
v___x_339_ = lean_box(2);
v___x_340_ = ((size_t)5ULL);
v___x_341_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1);
v___x_342_ = lean_usize_land(v_x_336_, v___x_341_);
v_j_343_ = lean_usize_to_nat(v___x_342_);
v___x_344_ = lean_array_get(v___x_339_, v_es_338_, v_j_343_);
lean_dec(v_j_343_);
lean_dec_ref(v_es_338_);
switch(lean_obj_tag(v___x_344_))
{
case 0:
{
lean_object* v_key_345_; uint8_t v___x_346_; 
v_key_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_key_345_);
lean_dec_ref(v___x_344_);
v___x_346_ = lean_name_eq(v_x_337_, v_key_345_);
lean_dec(v_key_345_);
return v___x_346_;
}
case 1:
{
lean_object* v_node_347_; size_t v___x_348_; 
v_node_347_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_node_347_);
lean_dec_ref(v___x_344_);
v___x_348_ = lean_usize_shift_right(v_x_336_, v___x_340_);
v_x_335_ = v_node_347_;
v_x_336_ = v___x_348_;
goto _start;
}
default: 
{
uint8_t v___x_350_; 
v___x_350_ = 0;
return v___x_350_;
}
}
}
else
{
lean_object* v_ks_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v_ks_351_ = lean_ctor_get(v_x_335_, 0);
lean_inc_ref(v_ks_351_);
lean_dec_ref(v_x_335_);
v___x_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg(v_ks_351_, v___x_352_, v_x_337_);
lean_dec_ref(v_ks_351_);
return v___x_353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___boxed(lean_object* v_x_354_, lean_object* v_x_355_, lean_object* v_x_356_){
_start:
{
size_t v_x_433__boxed_357_; uint8_t v_res_358_; lean_object* v_r_359_; 
v_x_433__boxed_357_ = lean_unbox_usize(v_x_355_);
lean_dec(v_x_355_);
v_res_358_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg(v_x_354_, v_x_433__boxed_357_, v_x_356_);
lean_dec(v_x_356_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_360_; uint64_t v___x_361_; 
v___x_360_ = lean_unsigned_to_nat(1723u);
v___x_361_ = lean_uint64_of_nat(v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg(lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
uint64_t v___y_365_; 
if (lean_obj_tag(v_x_363_) == 0)
{
uint64_t v___x_368_; 
v___x_368_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0);
v___y_365_ = v___x_368_;
goto v___jp_364_;
}
else
{
uint64_t v_hash_369_; 
v_hash_369_ = lean_ctor_get_uint64(v_x_363_, sizeof(void*)*2);
v___y_365_ = v_hash_369_;
goto v___jp_364_;
}
v___jp_364_:
{
size_t v___x_366_; uint8_t v___x_367_; 
v___x_366_ = lean_uint64_to_usize(v___y_365_);
v___x_367_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg(v_x_362_, v___x_366_, v_x_363_);
return v___x_367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___boxed(lean_object* v_x_370_, lean_object* v_x_371_){
_start:
{
uint8_t v_res_372_; lean_object* v_r_373_; 
v_res_372_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg(v_x_370_, v_x_371_);
lean_dec(v_x_371_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_374_, lean_object* v_x_375_, lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
lean_object* v_ks_378_; lean_object* v_vs_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_403_; 
v_ks_378_ = lean_ctor_get(v_x_374_, 0);
v_vs_379_ = lean_ctor_get(v_x_374_, 1);
v_isSharedCheck_403_ = !lean_is_exclusive(v_x_374_);
if (v_isSharedCheck_403_ == 0)
{
v___x_381_ = v_x_374_;
v_isShared_382_ = v_isSharedCheck_403_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_vs_379_);
lean_inc(v_ks_378_);
lean_dec(v_x_374_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_403_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = lean_array_get_size(v_ks_378_);
v___x_384_ = lean_nat_dec_lt(v_x_375_, v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
lean_dec(v_x_375_);
v___x_385_ = lean_array_push(v_ks_378_, v_x_376_);
v___x_386_ = lean_array_push(v_vs_379_, v_x_377_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 1, v___x_386_);
lean_ctor_set(v___x_381_, 0, v___x_385_);
v___x_388_ = v___x_381_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
else
{
lean_object* v_k_x27_390_; uint8_t v___x_391_; 
v_k_x27_390_ = lean_array_fget_borrowed(v_ks_378_, v_x_375_);
v___x_391_ = lean_name_eq(v_x_376_, v_k_x27_390_);
if (v___x_391_ == 0)
{
lean_object* v___x_393_; 
if (v_isShared_382_ == 0)
{
v___x_393_ = v___x_381_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_ks_378_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_vs_379_);
v___x_393_ = v_reuseFailAlloc_397_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_unsigned_to_nat(1u);
v___x_395_ = lean_nat_add(v_x_375_, v___x_394_);
lean_dec(v_x_375_);
v_x_374_ = v___x_393_;
v_x_375_ = v___x_395_;
goto _start;
}
}
else
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_398_ = lean_array_fset(v_ks_378_, v_x_375_, v_x_376_);
v___x_399_ = lean_array_fset(v_vs_379_, v_x_375_, v_x_377_);
lean_dec(v_x_375_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 1, v___x_399_);
lean_ctor_set(v___x_381_, 0, v___x_398_);
v___x_401_ = v___x_381_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4___redArg(lean_object* v_n_404_, lean_object* v_k_405_, lean_object* v_v_406_){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4_spec__5___redArg(v_n_404_, v___x_407_, v_k_405_, v_v_406_);
return v___x_408_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(lean_object* v_x_410_, size_t v_x_411_, size_t v_x_412_, lean_object* v_x_413_, lean_object* v_x_414_){
_start:
{
if (lean_obj_tag(v_x_410_) == 0)
{
lean_object* v_es_415_; size_t v___x_416_; size_t v___x_417_; size_t v___x_418_; size_t v___x_419_; lean_object* v_j_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v_es_415_ = lean_ctor_get(v_x_410_, 0);
v___x_416_ = ((size_t)5ULL);
v___x_417_ = ((size_t)1ULL);
v___x_418_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1);
v___x_419_ = lean_usize_land(v_x_411_, v___x_418_);
v_j_420_ = lean_usize_to_nat(v___x_419_);
v___x_421_ = lean_array_get_size(v_es_415_);
v___x_422_ = lean_nat_dec_lt(v_j_420_, v___x_421_);
if (v___x_422_ == 0)
{
lean_dec(v_j_420_);
lean_dec(v_x_414_);
lean_dec(v_x_413_);
return v_x_410_;
}
else
{
lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_459_; 
lean_inc_ref(v_es_415_);
v_isSharedCheck_459_ = !lean_is_exclusive(v_x_410_);
if (v_isSharedCheck_459_ == 0)
{
lean_object* v_unused_460_; 
v_unused_460_ = lean_ctor_get(v_x_410_, 0);
lean_dec(v_unused_460_);
v___x_424_ = v_x_410_;
v_isShared_425_ = v_isSharedCheck_459_;
goto v_resetjp_423_;
}
else
{
lean_dec(v_x_410_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_459_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v_v_426_; lean_object* v___x_427_; lean_object* v_xs_x27_428_; lean_object* v___y_430_; 
v_v_426_ = lean_array_fget(v_es_415_, v_j_420_);
v___x_427_ = lean_box(0);
v_xs_x27_428_ = lean_array_fset(v_es_415_, v_j_420_, v___x_427_);
switch(lean_obj_tag(v_v_426_))
{
case 0:
{
lean_object* v_key_435_; lean_object* v_val_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_446_; 
v_key_435_ = lean_ctor_get(v_v_426_, 0);
v_val_436_ = lean_ctor_get(v_v_426_, 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v_v_426_);
if (v_isSharedCheck_446_ == 0)
{
v___x_438_ = v_v_426_;
v_isShared_439_ = v_isSharedCheck_446_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_val_436_);
lean_inc(v_key_435_);
lean_dec(v_v_426_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_446_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
uint8_t v___x_440_; 
v___x_440_ = lean_name_eq(v_x_413_, v_key_435_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; lean_object* v___x_442_; 
lean_del_object(v___x_438_);
v___x_441_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_435_, v_val_436_, v_x_413_, v_x_414_);
v___x_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
v___y_430_ = v___x_442_;
goto v___jp_429_;
}
else
{
lean_object* v___x_444_; 
lean_dec(v_val_436_);
lean_dec(v_key_435_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 1, v_x_414_);
lean_ctor_set(v___x_438_, 0, v_x_413_);
v___x_444_ = v___x_438_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_x_413_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_x_414_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
v___y_430_ = v___x_444_;
goto v___jp_429_;
}
}
}
}
case 1:
{
lean_object* v_node_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_457_; 
v_node_447_ = lean_ctor_get(v_v_426_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v_v_426_);
if (v_isSharedCheck_457_ == 0)
{
v___x_449_ = v_v_426_;
v_isShared_450_ = v_isSharedCheck_457_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_node_447_);
lean_dec(v_v_426_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_457_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
size_t v___x_451_; size_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_451_ = lean_usize_shift_right(v_x_411_, v___x_416_);
v___x_452_ = lean_usize_add(v_x_412_, v___x_417_);
v___x_453_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_node_447_, v___x_451_, v___x_452_, v_x_413_, v_x_414_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_453_);
v___x_455_ = v___x_449_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
v___y_430_ = v___x_455_;
goto v___jp_429_;
}
}
}
default: 
{
lean_object* v___x_458_; 
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v_x_413_);
lean_ctor_set(v___x_458_, 1, v_x_414_);
v___y_430_ = v___x_458_;
goto v___jp_429_;
}
}
v___jp_429_:
{
lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_431_ = lean_array_fset(v_xs_x27_428_, v_j_420_, v___y_430_);
lean_dec(v_j_420_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_431_);
v___x_433_ = v___x_424_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
else
{
lean_object* v_ks_461_; lean_object* v_vs_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_482_; 
v_ks_461_ = lean_ctor_get(v_x_410_, 0);
v_vs_462_ = lean_ctor_get(v_x_410_, 1);
v_isSharedCheck_482_ = !lean_is_exclusive(v_x_410_);
if (v_isSharedCheck_482_ == 0)
{
v___x_464_ = v_x_410_;
v_isShared_465_ = v_isSharedCheck_482_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_vs_462_);
lean_inc(v_ks_461_);
lean_dec(v_x_410_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_482_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_ks_461_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_vs_462_);
v___x_467_ = v_reuseFailAlloc_481_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v_newNode_468_; uint8_t v___y_470_; size_t v___x_476_; uint8_t v___x_477_; 
v_newNode_468_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4___redArg(v___x_467_, v_x_413_, v_x_414_);
v___x_476_ = ((size_t)7ULL);
v___x_477_ = lean_usize_dec_le(v___x_476_, v_x_412_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_478_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_468_);
v___x_479_ = lean_unsigned_to_nat(4u);
v___x_480_ = lean_nat_dec_lt(v___x_478_, v___x_479_);
lean_dec(v___x_478_);
v___y_470_ = v___x_480_;
goto v___jp_469_;
}
else
{
v___y_470_ = v___x_477_;
goto v___jp_469_;
}
v___jp_469_:
{
if (v___y_470_ == 0)
{
lean_object* v_ks_471_; lean_object* v_vs_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v_ks_471_ = lean_ctor_get(v_newNode_468_, 0);
lean_inc_ref(v_ks_471_);
v_vs_472_ = lean_ctor_get(v_newNode_468_, 1);
lean_inc_ref(v_vs_472_);
lean_dec_ref(v_newNode_468_);
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0);
v___x_475_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg(v_x_412_, v_ks_471_, v_vs_472_, v___x_473_, v___x_474_);
lean_dec_ref(v_vs_472_);
lean_dec_ref(v_ks_471_);
return v___x_475_;
}
else
{
return v_newNode_468_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg(size_t v_depth_483_, lean_object* v_keys_484_, lean_object* v_vals_485_, lean_object* v_i_486_, lean_object* v_entries_487_){
_start:
{
lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_488_ = lean_array_get_size(v_keys_484_);
v___x_489_ = lean_nat_dec_lt(v_i_486_, v___x_488_);
if (v___x_489_ == 0)
{
lean_dec(v_i_486_);
return v_entries_487_;
}
else
{
lean_object* v_k_490_; lean_object* v_v_491_; uint64_t v___y_493_; 
v_k_490_ = lean_array_fget_borrowed(v_keys_484_, v_i_486_);
v_v_491_ = lean_array_fget_borrowed(v_vals_485_, v_i_486_);
if (lean_obj_tag(v_k_490_) == 0)
{
uint64_t v___x_504_; 
v___x_504_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0);
v___y_493_ = v___x_504_;
goto v___jp_492_;
}
else
{
uint64_t v_hash_505_; 
v_hash_505_ = lean_ctor_get_uint64(v_k_490_, sizeof(void*)*2);
v___y_493_ = v_hash_505_;
goto v___jp_492_;
}
v___jp_492_:
{
size_t v_h_494_; size_t v___x_495_; lean_object* v___x_496_; size_t v___x_497_; size_t v___x_498_; size_t v___x_499_; size_t v_h_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v_h_494_ = lean_uint64_to_usize(v___y_493_);
v___x_495_ = ((size_t)5ULL);
v___x_496_ = lean_unsigned_to_nat(1u);
v___x_497_ = ((size_t)1ULL);
v___x_498_ = lean_usize_sub(v_depth_483_, v___x_497_);
v___x_499_ = lean_usize_mul(v___x_495_, v___x_498_);
v_h_500_ = lean_usize_shift_right(v_h_494_, v___x_499_);
v___x_501_ = lean_nat_add(v_i_486_, v___x_496_);
lean_dec(v_i_486_);
lean_inc(v_v_491_);
lean_inc(v_k_490_);
v___x_502_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_entries_487_, v_h_500_, v_depth_483_, v_k_490_, v_v_491_);
v_i_486_ = v___x_501_;
v_entries_487_ = v___x_502_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_506_, lean_object* v_keys_507_, lean_object* v_vals_508_, lean_object* v_i_509_, lean_object* v_entries_510_){
_start:
{
size_t v_depth_boxed_511_; lean_object* v_res_512_; 
v_depth_boxed_511_ = lean_unbox_usize(v_depth_506_);
lean_dec(v_depth_506_);
v_res_512_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg(v_depth_boxed_511_, v_keys_507_, v_vals_508_, v_i_509_, v_entries_510_);
lean_dec_ref(v_vals_508_);
lean_dec_ref(v_keys_507_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___boxed(lean_object* v_x_513_, lean_object* v_x_514_, lean_object* v_x_515_, lean_object* v_x_516_, lean_object* v_x_517_){
_start:
{
size_t v_x_589__boxed_518_; size_t v_x_590__boxed_519_; lean_object* v_res_520_; 
v_x_589__boxed_518_ = lean_unbox_usize(v_x_514_);
lean_dec(v_x_514_);
v_x_590__boxed_519_ = lean_unbox_usize(v_x_515_);
lean_dec(v_x_515_);
v_res_520_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_x_513_, v_x_589__boxed_518_, v_x_590__boxed_519_, v_x_516_, v_x_517_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(lean_object* v_x_521_, lean_object* v_x_522_, lean_object* v_x_523_){
_start:
{
uint64_t v___y_525_; 
if (lean_obj_tag(v_x_522_) == 0)
{
uint64_t v___x_529_; 
v___x_529_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0);
v___y_525_ = v___x_529_;
goto v___jp_524_;
}
else
{
uint64_t v_hash_530_; 
v_hash_530_ = lean_ctor_get_uint64(v_x_522_, sizeof(void*)*2);
v___y_525_ = v_hash_530_;
goto v___jp_524_;
}
v___jp_524_:
{
size_t v___x_526_; size_t v___x_527_; lean_object* v___x_528_; 
v___x_526_ = lean_uint64_to_usize(v___y_525_);
v___x_527_ = ((size_t)1ULL);
v___x_528_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_x_521_, v___x_526_, v___x_527_, v_x_522_, v_x_523_);
return v___x_528_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___lam__0(lean_object* v_oldState_531_, lean_object* v_otherState_532_, lean_object* v_k_533_, lean_object* v_v_534_){
_start:
{
uint8_t v___x_535_; 
v___x_535_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg(v_oldState_531_, v_k_533_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_otherState_532_, v_k_533_, v_v_534_);
return v___x_536_;
}
else
{
lean_dec(v_v_534_);
lean_dec(v_k_533_);
return v_otherState_532_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg(lean_object* v_oldState_537_, lean_object* v_newState_538_, lean_object* v_otherState_539_){
_start:
{
lean_object* v___f_540_; lean_object* v___x_541_; 
v___f_540_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_540_, 0, v_oldState_537_);
v___x_541_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_newState_538_, v___f_540_, v_otherState_539_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___boxed(lean_object* v_oldState_542_, lean_object* v_newState_543_, lean_object* v_otherState_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg(v_oldState_542_, v_newState_543_, v_otherState_544_);
lean_dec_ref(v_newState_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn(lean_object* v_00_u03b2_546_, uint8_t v_phase_547_, lean_object* v_oldState_548_, lean_object* v_newState_549_, lean_object* v_x_550_, lean_object* v_otherState_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg(v_oldState_548_, v_newState_549_, v_otherState_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___boxed(lean_object* v_00_u03b2_553_, lean_object* v_phase_554_, lean_object* v_oldState_555_, lean_object* v_newState_556_, lean_object* v_x_557_, lean_object* v_otherState_558_){
_start:
{
uint8_t v_phase_boxed_559_; lean_object* v_res_560_; 
v_phase_boxed_559_ = lean_unbox(v_phase_554_);
v_res_560_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn(v_00_u03b2_553_, v_phase_boxed_559_, v_oldState_555_, v_newState_556_, v_x_557_, v_otherState_558_);
lean_dec(v_x_557_);
lean_dec_ref(v_newState_556_);
return v_res_560_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0(lean_object* v_00_u03b2_561_, lean_object* v_x_562_, lean_object* v_x_563_){
_start:
{
uint8_t v___x_564_; 
v___x_564_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg(v_x_562_, v_x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___boxed(lean_object* v_00_u03b2_565_, lean_object* v_x_566_, lean_object* v_x_567_){
_start:
{
uint8_t v_res_568_; lean_object* v_r_569_; 
v_res_568_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0(v_00_u03b2_565_, v_x_566_, v_x_567_);
lean_dec(v_x_567_);
v_r_569_ = lean_box(v_res_568_);
return v_r_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1(lean_object* v_00_u03b2_570_, lean_object* v_x_571_, lean_object* v_x_572_, lean_object* v_x_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_x_571_, v_x_572_, v_x_573_);
return v___x_574_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0(lean_object* v_00_u03b2_575_, lean_object* v_x_576_, size_t v_x_577_, lean_object* v_x_578_){
_start:
{
uint8_t v___x_579_; 
v___x_579_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg(v_x_576_, v_x_577_, v_x_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___boxed(lean_object* v_00_u03b2_580_, lean_object* v_x_581_, lean_object* v_x_582_, lean_object* v_x_583_){
_start:
{
size_t v_x_797__boxed_584_; uint8_t v_res_585_; lean_object* v_r_586_; 
v_x_797__boxed_584_ = lean_unbox_usize(v_x_582_);
lean_dec(v_x_582_);
v_res_585_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0(v_00_u03b2_580_, v_x_581_, v_x_797__boxed_584_, v_x_583_);
lean_dec(v_x_583_);
v_r_586_ = lean_box(v_res_585_);
return v_r_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2(lean_object* v_00_u03b2_587_, lean_object* v_x_588_, size_t v_x_589_, size_t v_x_590_, lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_x_588_, v_x_589_, v_x_590_, v_x_591_, v_x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___boxed(lean_object* v_00_u03b2_594_, lean_object* v_x_595_, lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v_x_598_, lean_object* v_x_599_){
_start:
{
size_t v_x_808__boxed_600_; size_t v_x_809__boxed_601_; lean_object* v_res_602_; 
v_x_808__boxed_600_ = lean_unbox_usize(v_x_596_);
lean_dec(v_x_596_);
v_x_809__boxed_601_ = lean_unbox_usize(v_x_597_);
lean_dec(v_x_597_);
v_res_602_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2(v_00_u03b2_594_, v_x_595_, v_x_808__boxed_600_, v_x_809__boxed_601_, v_x_598_, v_x_599_);
return v_res_602_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_603_, lean_object* v_keys_604_, lean_object* v_vals_605_, lean_object* v_heq_606_, lean_object* v_i_607_, lean_object* v_k_608_){
_start:
{
uint8_t v___x_609_; 
v___x_609_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg(v_keys_604_, v_i_607_, v_k_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_610_, lean_object* v_keys_611_, lean_object* v_vals_612_, lean_object* v_heq_613_, lean_object* v_i_614_, lean_object* v_k_615_){
_start:
{
uint8_t v_res_616_; lean_object* v_r_617_; 
v_res_616_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1(v_00_u03b2_610_, v_keys_611_, v_vals_612_, v_heq_613_, v_i_614_, v_k_615_);
lean_dec(v_k_615_);
lean_dec_ref(v_vals_612_);
lean_dec_ref(v_keys_611_);
v_r_617_ = lean_box(v_res_616_);
return v_r_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_618_, lean_object* v_n_619_, lean_object* v_k_620_, lean_object* v_v_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4___redArg(v_n_619_, v_k_620_, v_v_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_623_, size_t v_depth_624_, lean_object* v_keys_625_, lean_object* v_vals_626_, lean_object* v_heq_627_, lean_object* v_i_628_, lean_object* v_entries_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg(v_depth_624_, v_keys_625_, v_vals_626_, v_i_628_, v_entries_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_631_, lean_object* v_depth_632_, lean_object* v_keys_633_, lean_object* v_vals_634_, lean_object* v_heq_635_, lean_object* v_i_636_, lean_object* v_entries_637_){
_start:
{
size_t v_depth_boxed_638_; lean_object* v_res_639_; 
v_depth_boxed_638_ = lean_unbox_usize(v_depth_632_);
lean_dec(v_depth_632_);
v_res_639_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5(v_00_u03b2_631_, v_depth_boxed_638_, v_keys_633_, v_vals_634_, v_heq_635_, v_i_636_, v_entries_637_);
lean_dec_ref(v_vals_634_);
lean_dec_ref(v_keys_633_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_640_, lean_object* v_x_641_, lean_object* v_x_642_, lean_object* v_x_643_, lean_object* v_x_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4_spec__5___redArg(v_x_641_, v_x_642_, v_x_643_, v_x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___lam__0(lean_object* v_count_646_, lean_object* v_x_647_, lean_object* v_x_648_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = lean_nat_add(v_count_646_, v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___lam__0___boxed(lean_object* v_count_651_, lean_object* v_x_652_, lean_object* v_x_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___lam__0(v_count_651_, v_x_652_, v_x_653_);
lean_dec(v_x_653_);
lean_dec(v_x_652_);
lean_dec(v_count_651_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg(lean_object* v_state_659_){
_start:
{
lean_object* v___f_660_; lean_object* v___x_661_; lean_object* v_numEntries_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___f_660_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__0));
v___x_661_ = lean_unsigned_to_nat(0u);
v_numEntries_662_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_state_659_, v___f_660_, v___x_661_);
v___x_663_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__2));
v___x_664_ = l_Nat_reprFast(v_numEntries_662_);
v___x_665_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
v___x_666_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_663_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___boxed(lean_object* v_state_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg(v_state_667_);
lean_dec_ref(v_state_667_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn(uint8_t v_pu_669_, lean_object* v_00_u03b2_670_, lean_object* v_state_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg(v_state_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___boxed(lean_object* v_pu_673_, lean_object* v_00_u03b2_674_, lean_object* v_state_675_){
_start:
{
uint8_t v_pu_boxed_676_; lean_object* v_res_677_; 
v_pu_boxed_676_ = lean_unbox(v_pu_673_);
v_res_677_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn(v_pu_boxed_676_, v_00_u03b2_674_, v_state_675_);
lean_dec_ref(v_state_675_);
return v_res_677_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___redArg(lean_object* v_a_678_, lean_object* v_b_679_){
_start:
{
lean_object* v_toSignature_680_; lean_object* v_toSignature_681_; lean_object* v_name_682_; lean_object* v_name_683_; uint8_t v___x_684_; 
v_toSignature_680_ = lean_ctor_get(v_a_678_, 0);
v_toSignature_681_ = lean_ctor_get(v_b_679_, 0);
v_name_682_ = lean_ctor_get(v_toSignature_680_, 0);
v_name_683_ = lean_ctor_get(v_toSignature_681_, 0);
v___x_684_ = l_Lean_Name_quickLt(v_name_682_, v_name_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___redArg___boxed(lean_object* v_a_685_, lean_object* v_b_686_){
_start:
{
uint8_t v_res_687_; lean_object* v_r_688_; 
v_res_687_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___redArg(v_a_685_, v_b_686_);
lean_dec_ref(v_b_686_);
lean_dec_ref(v_a_685_);
v_r_688_ = lean_box(v_res_687_);
return v_r_688_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt(uint8_t v_pu_689_, lean_object* v_a_690_, lean_object* v_b_691_){
_start:
{
lean_object* v_toSignature_692_; lean_object* v_toSignature_693_; lean_object* v_name_694_; lean_object* v_name_695_; uint8_t v___x_696_; 
v_toSignature_692_ = lean_ctor_get(v_a_690_, 0);
v_toSignature_693_ = lean_ctor_get(v_b_691_, 0);
v_name_694_ = lean_ctor_get(v_toSignature_692_, 0);
v_name_695_ = lean_ctor_get(v_toSignature_693_, 0);
v___x_696_ = l_Lean_Name_quickLt(v_name_694_, v_name_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___boxed(lean_object* v_pu_697_, lean_object* v_a_698_, lean_object* v_b_699_){
_start:
{
uint8_t v_pu_boxed_700_; uint8_t v_res_701_; lean_object* v_r_702_; 
v_pu_boxed_700_ = lean_unbox(v_pu_697_);
v_res_701_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt(v_pu_boxed_700_, v_a_698_, v_b_699_);
lean_dec_ref(v_b_699_);
lean_dec_ref(v_a_698_);
v_r_702_ = lean_box(v_res_701_);
return v_r_702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f(uint8_t v_pu_704_, lean_object* v_decls_705_, lean_object* v_declName_706_){
_start:
{
lean_object* v_tmpDecl_707_; lean_object* v_toSignature_708_; lean_object* v_value_709_; uint8_t v_recursive_710_; lean_object* v_inlineAttr_x3f_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_742_; 
v_tmpDecl_707_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default(v_pu_704_);
v_toSignature_708_ = lean_ctor_get(v_tmpDecl_707_, 0);
v_value_709_ = lean_ctor_get(v_tmpDecl_707_, 1);
v_recursive_710_ = lean_ctor_get_uint8(v_tmpDecl_707_, sizeof(void*)*3);
v_inlineAttr_x3f_711_ = lean_ctor_get(v_tmpDecl_707_, 2);
v_isSharedCheck_742_ = !lean_is_exclusive(v_tmpDecl_707_);
if (v_isSharedCheck_742_ == 0)
{
v___x_713_ = v_tmpDecl_707_;
v_isShared_714_ = v_isSharedCheck_742_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_inlineAttr_x3f_711_);
lean_inc(v_value_709_);
lean_inc(v_toSignature_708_);
lean_dec(v_tmpDecl_707_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_742_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v_levelParams_715_; lean_object* v_type_716_; lean_object* v_params_717_; uint8_t v_safe_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_740_; 
v_levelParams_715_ = lean_ctor_get(v_toSignature_708_, 1);
v_type_716_ = lean_ctor_get(v_toSignature_708_, 2);
v_params_717_ = lean_ctor_get(v_toSignature_708_, 3);
v_safe_718_ = lean_ctor_get_uint8(v_toSignature_708_, sizeof(void*)*4);
v_isSharedCheck_740_ = !lean_is_exclusive(v_toSignature_708_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; 
v_unused_741_ = lean_ctor_get(v_toSignature_708_, 0);
lean_dec(v_unused_741_);
v___x_720_ = v_toSignature_708_;
v_isShared_721_ = v_isSharedCheck_740_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_params_717_);
lean_inc(v_type_716_);
lean_inc(v_levelParams_715_);
lean_dec(v_toSignature_708_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_740_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_722_ = lean_unsigned_to_nat(0u);
v___x_723_ = lean_array_get_size(v_decls_705_);
v___x_724_ = lean_nat_dec_lt(v___x_722_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; 
lean_del_object(v___x_720_);
lean_dec_ref(v_params_717_);
lean_dec_ref(v_type_716_);
lean_dec(v_levelParams_715_);
lean_del_object(v___x_713_);
lean_dec(v_inlineAttr_x3f_711_);
lean_dec_ref(v_value_709_);
lean_dec(v_declName_706_);
v___x_725_ = lean_box(0);
return v___x_725_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_726_ = lean_unsigned_to_nat(1u);
v___x_727_ = lean_nat_sub(v___x_723_, v___x_726_);
v___x_728_ = lean_nat_dec_le(v___x_722_, v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; 
lean_dec(v___x_727_);
lean_del_object(v___x_720_);
lean_dec_ref(v_params_717_);
lean_dec_ref(v_type_716_);
lean_dec(v_levelParams_715_);
lean_del_object(v___x_713_);
lean_dec(v_inlineAttr_x3f_711_);
lean_dec_ref(v_value_709_);
lean_dec(v_declName_706_);
v___x_729_ = lean_box(0);
return v___x_729_;
}
else
{
lean_object* v___x_731_; 
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v_declName_706_);
v___x_731_ = v___x_720_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_declName_706_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_levelParams_715_);
lean_ctor_set(v_reuseFailAlloc_739_, 2, v_type_716_);
lean_ctor_set(v_reuseFailAlloc_739_, 3, v_params_717_);
lean_ctor_set_uint8(v_reuseFailAlloc_739_, sizeof(void*)*4, v_safe_718_);
v___x_731_ = v_reuseFailAlloc_739_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v_tmpDecl_733_; 
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v___x_731_);
v_tmpDecl_733_ = v___x_713_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_value_709_);
lean_ctor_set(v_reuseFailAlloc_738_, 2, v_inlineAttr_x3f_711_);
lean_ctor_set_uint8(v_reuseFailAlloc_738_, sizeof(void*)*3, v_recursive_710_);
v_tmpDecl_733_ = v_reuseFailAlloc_738_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_734_ = lean_box(v_pu_704_);
v___x_735_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___boxed), 3, 1);
lean_closure_set(v___x_735_, 0, v___x_734_);
v___x_736_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0));
v___x_737_ = l_Array_binSearchAux___redArg(v___x_735_, v___x_736_, v_decls_705_, v_tmpDecl_733_, v___x_722_, v___x_727_);
return v___x_737_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___boxed(lean_object* v_pu_743_, lean_object* v_decls_744_, lean_object* v_declName_745_){
_start:
{
uint8_t v_pu_boxed_746_; lean_object* v_res_747_; 
v_pu_boxed_746_ = lean_unbox(v_pu_743_);
v_res_747_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f(v_pu_boxed_746_, v_decls_744_, v_declName_745_);
lean_dec_ref(v_decls_744_);
return v_res_747_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__2(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_750_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__1));
v___x_751_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__0));
v___x_752_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_751_, v___x_750_);
return v___x_752_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__3(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__2, &l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__2);
v___x_754_ = l_Lean_instInhabitedPersistentEnvExtension(lean_box(0), lean_box(0), lean_box(0), v___x_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt(uint8_t v_pu_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__3, &l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__3_once, _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__3);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___boxed(lean_object* v_pu_757_){
_start:
{
uint8_t v_pu_boxed_758_; lean_object* v_res_759_; 
v_pu_boxed_758_ = lean_unbox(v_pu_757_);
v_res_759_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt(v_pu_boxed_758_);
return v_res_759_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__10));
v___x_787_ = l_Lean_mkAtom(v___x_786_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_788_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12);
v___x_789_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5));
v___x_790_ = lean_array_push(v___x_789_, v___x_788_);
return v___x_790_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__17));
v___x_800_ = l_Lean_mkAtom(v___x_799_);
return v___x_800_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18);
v___x_802_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5));
v___x_803_ = lean_array_push(v___x_802_, v___x_801_);
return v___x_803_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_804_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19);
v___x_805_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16));
v___x_806_ = lean_box(2);
v___x_807_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
lean_ctor_set(v___x_807_, 1, v___x_805_);
lean_ctor_set(v___x_807_, 2, v___x_804_);
return v___x_807_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_808_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20);
v___x_809_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13);
v___x_810_ = lean_array_push(v___x_809_, v___x_808_);
return v___x_810_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_811_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21);
v___x_812_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11));
v___x_813_ = lean_box(2);
v___x_814_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v___x_812_);
lean_ctor_set(v___x_814_, 2, v___x_811_);
return v___x_814_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_815_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22);
v___x_816_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5));
v___x_817_ = lean_array_push(v___x_816_, v___x_815_);
return v___x_817_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_818_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23);
v___x_819_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__9));
v___x_820_ = lean_box(2);
v___x_821_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
lean_ctor_set(v___x_821_, 1, v___x_819_);
lean_ctor_set(v___x_821_, 2, v___x_818_);
return v___x_821_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_822_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24);
v___x_823_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5));
v___x_824_ = lean_array_push(v___x_823_, v___x_822_);
return v___x_824_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_825_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25);
v___x_826_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7));
v___x_827_ = lean_box(2);
v___x_828_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v___x_826_);
lean_ctor_set(v___x_828_, 2, v___x_825_);
return v___x_828_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_829_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26);
v___x_830_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5));
v___x_831_ = lean_array_push(v___x_830_, v___x_829_);
return v___x_831_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_832_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27);
v___x_833_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4));
v___x_834_ = lean_box(2);
v___x_835_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v___x_833_);
lean_ctor_set(v___x_835_, 2, v___x_832_);
return v___x_835_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1(void){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__0(lean_object* v_s_837_, lean_object* v_decl_838_){
_start:
{
lean_object* v_toSignature_839_; lean_object* v_name_840_; lean_object* v___x_841_; 
v_toSignature_839_ = lean_ctor_get(v_decl_838_, 0);
v_name_840_ = lean_ctor_get(v_toSignature_839_, 0);
lean_inc(v_name_840_);
v___x_841_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_s_837_, v_name_840_, v_decl_838_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__1(lean_object* v_x_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___lam__1___closed__0));
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__1___boxed(lean_object* v_x_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__1(v_x_846_);
lean_dec_ref(v_x_846_);
return v_res_847_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_mkDeclExt___lam__2(lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_toSignature_850_; lean_object* v_toSignature_851_; lean_object* v_name_852_; lean_object* v_name_853_; uint8_t v___x_854_; 
v_toSignature_850_ = lean_ctor_get(v___y_848_, 0);
v_toSignature_851_ = lean_ctor_get(v___y_849_, 0);
v_name_852_ = lean_ctor_get(v_toSignature_850_, 0);
v_name_853_ = lean_ctor_get(v_toSignature_851_, 0);
v___x_854_ = l_Lean_Name_quickLt(v_name_852_, v_name_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__2___boxed(lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
uint8_t v_res_857_; lean_object* v_r_858_; 
v_res_857_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__2(v___y_855_, v___y_856_);
lean_dec_ref(v___y_856_);
lean_dec_ref(v___y_855_);
v_r_858_ = lean_box(v_res_857_);
return v_r_858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(lean_object* v_env_864_, uint8_t v_phase_865_, lean_object* v_as_866_, size_t v_i_867_, size_t v_stop_868_, lean_object* v_b_869_){
_start:
{
lean_object* v___y_871_; uint8_t v___x_875_; 
v___x_875_ = lean_usize_dec_eq(v_i_867_, v_stop_868_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; lean_object* v_toSignature_877_; uint8_t v_recursive_878_; lean_object* v_inlineAttr_x3f_879_; lean_object* v_name_880_; uint8_t v___x_881_; 
v___x_876_ = lean_array_uget(v_as_866_, v_i_867_);
v_toSignature_877_ = lean_ctor_get(v___x_876_, 0);
v_recursive_878_ = lean_ctor_get_uint8(v___x_876_, sizeof(void*)*3);
v_inlineAttr_x3f_879_ = lean_ctor_get(v___x_876_, 2);
v_name_880_ = lean_ctor_get(v_toSignature_877_, 0);
lean_inc_ref(v_env_864_);
v___x_881_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_864_, v_name_880_);
if (v___x_881_ == 0)
{
lean_dec(v___x_876_);
v___y_871_ = v_b_869_;
goto v___jp_870_;
}
else
{
uint8_t v___x_882_; 
lean_inc_ref(v_env_864_);
v___x_882_ = l_Lean_Compiler_LCNF_isDeclTransparent(v_env_864_, v_phase_865_, v_name_880_);
if (v___x_882_ == 0)
{
lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_891_; 
lean_inc(v_inlineAttr_x3f_879_);
lean_inc_ref(v_toSignature_877_);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_891_ == 0)
{
lean_object* v_unused_892_; lean_object* v_unused_893_; lean_object* v_unused_894_; 
v_unused_892_ = lean_ctor_get(v___x_876_, 2);
lean_dec(v_unused_892_);
v_unused_893_ = lean_ctor_get(v___x_876_, 1);
lean_dec(v_unused_893_);
v_unused_894_ = lean_ctor_get(v___x_876_, 0);
lean_dec(v_unused_894_);
v___x_884_ = v___x_876_;
v_isShared_885_ = v_isSharedCheck_891_;
goto v_resetjp_883_;
}
else
{
lean_dec(v___x_876_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_891_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_886_; lean_object* v___x_888_; 
v___x_886_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__1));
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 1, v___x_886_);
v___x_888_ = v___x_884_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_toSignature_877_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_890_, 2, v_inlineAttr_x3f_879_);
lean_ctor_set_uint8(v_reuseFailAlloc_890_, sizeof(void*)*3, v_recursive_878_);
v___x_888_ = v_reuseFailAlloc_890_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_889_; 
v___x_889_ = lean_array_push(v_b_869_, v___x_888_);
v___y_871_ = v___x_889_;
goto v___jp_870_;
}
}
}
else
{
lean_object* v___x_895_; 
v___x_895_ = lean_array_push(v_b_869_, v___x_876_);
v___y_871_ = v___x_895_;
goto v___jp_870_;
}
}
}
else
{
lean_dec_ref(v_env_864_);
return v_b_869_;
}
v___jp_870_:
{
size_t v___x_872_; size_t v___x_873_; 
v___x_872_ = ((size_t)1ULL);
v___x_873_ = lean_usize_add(v_i_867_, v___x_872_);
v_i_867_ = v___x_873_;
v_b_869_ = v___y_871_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___boxed(lean_object* v_env_896_, lean_object* v_phase_897_, lean_object* v_as_898_, lean_object* v_i_899_, lean_object* v_stop_900_, lean_object* v_b_901_){
_start:
{
uint8_t v_phase_boxed_902_; size_t v_i_boxed_903_; size_t v_stop_boxed_904_; lean_object* v_res_905_; 
v_phase_boxed_902_ = lean_unbox(v_phase_897_);
v_i_boxed_903_ = lean_unbox_usize(v_i_899_);
lean_dec(v_i_899_);
v_stop_boxed_904_ = lean_unbox_usize(v_stop_900_);
lean_dec(v_stop_900_);
v_res_905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(v_env_896_, v_phase_boxed_902_, v_as_898_, v_i_boxed_903_, v_stop_boxed_904_, v_b_901_);
lean_dec_ref(v_as_898_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0(lean_object* v_env_906_, uint8_t v_phase_907_, uint8_t v___x_908_, lean_object* v_as_909_, lean_object* v_start_910_, lean_object* v_stop_911_){
_start:
{
lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_912_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___lam__1___closed__0));
v___x_913_ = lean_nat_dec_lt(v_start_910_, v_stop_911_);
if (v___x_913_ == 0)
{
lean_dec_ref(v_env_906_);
return v___x_912_;
}
else
{
lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_914_ = lean_array_get_size(v_as_909_);
v___x_915_ = lean_nat_dec_le(v_stop_911_, v___x_914_);
if (v___x_915_ == 0)
{
uint8_t v___x_916_; 
v___x_916_ = lean_nat_dec_lt(v_start_910_, v___x_914_);
if (v___x_916_ == 0)
{
lean_dec_ref(v_env_906_);
return v___x_912_;
}
else
{
size_t v___x_917_; size_t v___x_918_; lean_object* v___x_919_; 
v___x_917_ = lean_usize_of_nat(v_start_910_);
v___x_918_ = lean_usize_of_nat(v___x_914_);
v___x_919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(v_env_906_, v_phase_907_, v_as_909_, v___x_917_, v___x_918_, v___x_912_);
return v___x_919_;
}
}
else
{
size_t v___x_920_; size_t v___x_921_; lean_object* v___x_922_; 
v___x_920_ = lean_usize_of_nat(v_start_910_);
v___x_921_ = lean_usize_of_nat(v_stop_911_);
v___x_922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(v_env_906_, v_phase_907_, v_as_909_, v___x_920_, v___x_921_, v___x_912_);
return v___x_922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0___boxed(lean_object* v_env_923_, lean_object* v_phase_924_, lean_object* v___x_925_, lean_object* v_as_926_, lean_object* v_start_927_, lean_object* v_stop_928_){
_start:
{
uint8_t v_phase_boxed_929_; uint8_t v___x_1371__boxed_930_; lean_object* v_res_931_; 
v_phase_boxed_929_ = lean_unbox(v_phase_924_);
v___x_1371__boxed_930_ = lean_unbox(v___x_925_);
v_res_931_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0(v_env_923_, v_phase_boxed_929_, v___x_1371__boxed_930_, v_as_926_, v_start_927_, v_stop_928_);
lean_dec(v_stop_928_);
lean_dec(v_start_927_);
lean_dec_ref(v_as_926_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__3(lean_object* v___f_932_, uint8_t v_phase_933_, lean_object* v_env_934_, lean_object* v_s_935_, uint8_t v_level_936_){
_start:
{
lean_object* v_entries_937_; uint8_t v___x_938_; uint8_t v___x_939_; 
v_entries_937_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(v_s_935_, v___f_932_);
v___x_938_ = 2;
v___x_939_ = l_Lean_instDecidableEqOLeanLevel(v_level_936_, v___x_938_);
if (v___x_939_ == 0)
{
uint8_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v_entries_943_; 
v___x_940_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_933_);
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = lean_array_get_size(v_entries_937_);
v_entries_943_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0(v_env_934_, v_phase_933_, v___x_940_, v_entries_937_, v___x_941_, v___x_942_);
lean_dec_ref(v_entries_937_);
return v_entries_943_;
}
else
{
lean_dec_ref(v_env_934_);
return v_entries_937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__3___boxed(lean_object* v___f_944_, lean_object* v_phase_945_, lean_object* v_env_946_, lean_object* v_s_947_, lean_object* v_level_948_){
_start:
{
uint8_t v_phase_boxed_949_; uint8_t v_level_boxed_950_; lean_object* v_res_951_; 
v_phase_boxed_949_ = lean_unbox(v_phase_945_);
v_level_boxed_950_ = lean_unbox(v_level_948_);
v_res_951_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__3(v___f_944_, v_phase_boxed_949_, v_env_946_, v_s_947_, v_level_boxed_950_);
lean_dec_ref(v_s_947_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__4(lean_object* v___x_952_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__4___boxed(lean_object* v___x_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__4(v___x_955_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__5(lean_object* v___x_958_, lean_object* v_x_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v___x_958_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__5___boxed(lean_object* v___x_963_, lean_object* v_x_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__5(v___x_963_, v_x_964_, v___y_965_);
lean_dec_ref(v___y_965_);
lean_dec_ref(v_x_964_);
return v_res_967_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__3(void){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_971_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__4(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__3, &l_Lean_Compiler_LCNF_mkDeclExt___closed__3_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__3);
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
return v___x_973_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__5(void){
_start:
{
lean_object* v___x_974_; lean_object* v___f_975_; 
v___x_974_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__4, &l_Lean_Compiler_LCNF_mkDeclExt___closed__4_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__4);
v___f_975_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkDeclExt___lam__4___boxed), 2, 1);
lean_closure_set(v___f_975_, 0, v___x_974_);
return v___f_975_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__6(void){
_start:
{
lean_object* v___x_976_; lean_object* v___f_977_; 
v___x_976_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__4, &l_Lean_Compiler_LCNF_mkDeclExt___closed__4_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__4);
v___f_977_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkDeclExt___lam__5___boxed), 4, 1);
lean_closure_set(v___f_977_, 0, v___x_976_);
return v___f_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt(uint8_t v_phase_978_, lean_object* v_name_979_){
_start:
{
lean_object* v___f_981_; lean_object* v___f_982_; lean_object* v___f_983_; lean_object* v___x_984_; lean_object* v___f_985_; lean_object* v___f_986_; lean_object* v___f_987_; uint8_t v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___f_981_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___closed__0));
v___f_982_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___closed__1));
v___f_983_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___closed__2));
v___x_984_ = lean_box(v_phase_978_);
v___f_985_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkDeclExt___lam__3___boxed), 5, 2);
lean_closure_set(v___f_985_, 0, v___f_983_);
lean_closure_set(v___f_985_, 1, v___x_984_);
v___f_986_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__5, &l_Lean_Compiler_LCNF_mkDeclExt___closed__5_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__5);
v___f_987_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__6, &l_Lean_Compiler_LCNF_mkDeclExt___closed__6_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__6);
v___x_988_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_978_);
v___x_989_ = lean_box(v___x_988_);
v___x_990_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___boxed), 3, 2);
lean_closure_set(v___x_990_, 0, v___x_989_);
lean_closure_set(v___x_990_, 1, lean_box(0));
v___x_991_ = lean_box(0);
v___x_992_ = lean_box(v_phase_978_);
v___x_993_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___boxed), 6, 2);
lean_closure_set(v___x_993_, 0, lean_box(0));
lean_closure_set(v___x_993_, 1, v___x_992_);
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
v___x_995_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_995_, 0, v_name_979_);
lean_ctor_set(v___x_995_, 1, v___f_986_);
lean_ctor_set(v___x_995_, 2, v___f_987_);
lean_ctor_set(v___x_995_, 3, v___f_981_);
lean_ctor_set(v___x_995_, 4, v___f_985_);
lean_ctor_set(v___x_995_, 5, v___x_990_);
lean_ctor_set(v___x_995_, 6, v___x_991_);
lean_ctor_set(v___x_995_, 7, v___x_994_);
v___x_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set(v___x_996_, 1, v___f_982_);
v___x_997_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___boxed(lean_object* v_phase_998_, lean_object* v_name_999_, lean_object* v_a_1000_){
_start:
{
uint8_t v_phase_boxed_1001_; lean_object* v_res_1002_; 
v_phase_boxed_1001_ = lean_unbox(v_phase_998_);
v_res_1002_ = l_Lean_Compiler_LCNF_mkDeclExt(v_phase_boxed_1001_, v_name_999_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0(lean_object* v_env_1003_, uint8_t v_phase_1004_, uint8_t v___x_1005_, lean_object* v_as_1006_, size_t v_i_1007_, size_t v_stop_1008_, lean_object* v_b_1009_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(v_env_1003_, v_phase_1004_, v_as_1006_, v_i_1007_, v_stop_1008_, v_b_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___boxed(lean_object* v_env_1011_, lean_object* v_phase_1012_, lean_object* v___x_1013_, lean_object* v_as_1014_, lean_object* v_i_1015_, lean_object* v_stop_1016_, lean_object* v_b_1017_){
_start:
{
uint8_t v_phase_boxed_1018_; uint8_t v___x_1499__boxed_1019_; size_t v_i_boxed_1020_; size_t v_stop_boxed_1021_; lean_object* v_res_1022_; 
v_phase_boxed_1018_ = lean_unbox(v_phase_1012_);
v___x_1499__boxed_1019_ = lean_unbox(v___x_1013_);
v_i_boxed_1020_ = lean_unbox_usize(v_i_1015_);
lean_dec(v_i_1015_);
v_stop_boxed_1021_ = lean_unbox_usize(v_stop_1016_);
lean_dec(v_stop_1016_);
v_res_1022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0(v_env_1011_, v_phase_boxed_1018_, v___x_1499__boxed_1019_, v_as_1014_, v_i_boxed_1020_, v_stop_boxed_1021_, v_b_1017_);
lean_dec_ref(v_as_1014_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1032_ = 0;
v___x_1033_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_));
v___x_1034_ = l_Lean_Compiler_LCNF_mkDeclExt(v___x_1032_, v___x_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2____boxed(lean_object* v_a_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_();
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1044_ = 1;
v___x_1045_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_));
v___x_1046_ = l_Lean_Compiler_LCNF_mkDeclExt(v___x_1044_, v___x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2____boxed(lean_object* v_a_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_();
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___f_1055_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__5, &l_Lean_Compiler_LCNF_mkDeclExt___closed__5_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__5);
v___x_1056_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_));
v___x_1057_ = lean_box(0);
v___x_1058_ = l_Lean_registerEnvExtension___redArg(v___f_1055_, v___x_1056_, v___x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2____boxed(lean_object* v_a_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_();
return v_res_1060_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___closed__0(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1061_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__1));
v___x_1062_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__0));
v___x_1063_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_1062_, v___x_1061_);
return v___x_1063_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___closed__1(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedSigExt___closed__0, &l_Lean_Compiler_LCNF_instInhabitedSigExt___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___closed__0);
v___x_1065_ = l_Lean_instInhabitedPersistentEnvExtension(lean_box(0), lean_box(0), lean_box(0), v___x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt(uint8_t v_pu_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedSigExt___closed__1, &l_Lean_Compiler_LCNF_instInhabitedSigExt___closed__1_once, _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___closed__1);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___boxed(lean_object* v_pu_1068_){
_start:
{
uint8_t v_pu_boxed_1069_; lean_object* v_res_1070_; 
v_pu_boxed_1069_ = lean_unbox(v_pu_1068_);
v_res_1070_ = l_Lean_Compiler_LCNF_instInhabitedSigExt(v_pu_boxed_1069_);
return v_res_1070_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___redArg(lean_object* v_a_1071_, lean_object* v_b_1072_){
_start:
{
lean_object* v_name_1073_; lean_object* v_name_1074_; uint8_t v___x_1075_; 
v_name_1073_ = lean_ctor_get(v_a_1071_, 0);
v_name_1074_ = lean_ctor_get(v_b_1072_, 0);
v___x_1075_ = l_Lean_Name_quickLt(v_name_1073_, v_name_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___redArg___boxed(lean_object* v_a_1076_, lean_object* v_b_1077_){
_start:
{
uint8_t v_res_1078_; lean_object* v_r_1079_; 
v_res_1078_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___redArg(v_a_1076_, v_b_1077_);
lean_dec_ref(v_b_1077_);
lean_dec_ref(v_a_1076_);
v_r_1079_ = lean_box(v_res_1078_);
return v_r_1079_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt(uint8_t v_pu_1080_, lean_object* v_a_1081_, lean_object* v_b_1082_){
_start:
{
lean_object* v_name_1083_; lean_object* v_name_1084_; uint8_t v___x_1085_; 
v_name_1083_ = lean_ctor_get(v_a_1081_, 0);
v_name_1084_ = lean_ctor_get(v_b_1082_, 0);
v___x_1085_ = l_Lean_Name_quickLt(v_name_1083_, v_name_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___boxed(lean_object* v_pu_1086_, lean_object* v_a_1087_, lean_object* v_b_1088_){
_start:
{
uint8_t v_pu_boxed_1089_; uint8_t v_res_1090_; lean_object* v_r_1091_; 
v_pu_boxed_1089_ = lean_unbox(v_pu_1086_);
v_res_1090_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt(v_pu_boxed_1089_, v_a_1087_, v_b_1088_);
lean_dec_ref(v_b_1088_);
lean_dec_ref(v_a_1087_);
v_r_1091_ = lean_box(v_res_1090_);
return v_r_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f(uint8_t v_pu_1093_, lean_object* v_sigs_1094_, lean_object* v_declName_1095_){
_start:
{
lean_object* v_tmpSig_1096_; lean_object* v_levelParams_1097_; lean_object* v_type_1098_; lean_object* v_params_1099_; uint8_t v_safe_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1119_; 
v_tmpSig_1096_ = l_Lean_Compiler_LCNF_instInhabitedSignature_default(v_pu_1093_);
v_levelParams_1097_ = lean_ctor_get(v_tmpSig_1096_, 1);
v_type_1098_ = lean_ctor_get(v_tmpSig_1096_, 2);
v_params_1099_ = lean_ctor_get(v_tmpSig_1096_, 3);
v_safe_1100_ = lean_ctor_get_uint8(v_tmpSig_1096_, sizeof(void*)*4);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_tmpSig_1096_);
if (v_isSharedCheck_1119_ == 0)
{
lean_object* v_unused_1120_; 
v_unused_1120_ = lean_ctor_get(v_tmpSig_1096_, 0);
lean_dec(v_unused_1120_);
v___x_1102_ = v_tmpSig_1096_;
v_isShared_1103_ = v_isSharedCheck_1119_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_params_1099_);
lean_inc(v_type_1098_);
lean_inc(v_levelParams_1097_);
lean_dec(v_tmpSig_1096_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1119_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1104_ = lean_unsigned_to_nat(0u);
v___x_1105_ = lean_array_get_size(v_sigs_1094_);
v___x_1106_ = lean_nat_dec_lt(v___x_1104_, v___x_1105_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; 
lean_del_object(v___x_1102_);
lean_dec_ref(v_params_1099_);
lean_dec_ref(v_type_1098_);
lean_dec(v_levelParams_1097_);
lean_dec(v_declName_1095_);
v___x_1107_ = lean_box(0);
return v___x_1107_;
}
else
{
lean_object* v___x_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1108_ = lean_unsigned_to_nat(1u);
v___x_1109_ = lean_nat_sub(v___x_1105_, v___x_1108_);
v___x_1110_ = lean_nat_dec_le(v___x_1104_, v___x_1109_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; 
lean_dec(v___x_1109_);
lean_del_object(v___x_1102_);
lean_dec_ref(v_params_1099_);
lean_dec_ref(v_type_1098_);
lean_dec(v_levelParams_1097_);
lean_dec(v_declName_1095_);
v___x_1111_ = lean_box(0);
return v___x_1111_;
}
else
{
lean_object* v_tmpSig_1113_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 0, v_declName_1095_);
v_tmpSig_1113_ = v___x_1102_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_declName_1095_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_levelParams_1097_);
lean_ctor_set(v_reuseFailAlloc_1118_, 2, v_type_1098_);
lean_ctor_set(v_reuseFailAlloc_1118_, 3, v_params_1099_);
lean_ctor_set_uint8(v_reuseFailAlloc_1118_, sizeof(void*)*4, v_safe_1100_);
v_tmpSig_1113_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1114_ = lean_box(v_pu_1093_);
v___x_1115_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___boxed), 3, 1);
lean_closure_set(v___x_1115_, 0, v___x_1114_);
v___x_1116_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0));
v___x_1117_ = l_Array_binSearchAux___redArg(v___x_1115_, v___x_1116_, v_sigs_1094_, v_tmpSig_1113_, v___x_1104_, v___x_1109_);
return v___x_1117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___boxed(lean_object* v_pu_1121_, lean_object* v_sigs_1122_, lean_object* v_declName_1123_){
_start:
{
uint8_t v_pu_boxed_1124_; lean_object* v_res_1125_; 
v_pu_boxed_1124_ = lean_unbox(v_pu_1121_);
v_res_1125_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f(v_pu_boxed_1124_, v_sigs_1122_, v_declName_1123_);
lean_dec_ref(v_sigs_1122_);
return v_res_1125_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkSigDeclExt___auto__1(void){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__0(lean_object* v_s_1127_, lean_object* v_sig_1128_){
_start:
{
lean_object* v_name_1129_; lean_object* v___x_1130_; 
v_name_1129_ = lean_ctor_get(v_sig_1128_, 0);
lean_inc(v_name_1129_);
v___x_1130_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_s_1127_, v_name_1129_, v_sig_1128_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1(lean_object* v_x_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1___closed__0));
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1___boxed(lean_object* v_x_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1(v_x_1135_);
lean_dec_ref(v_x_1135_);
return v_res_1136_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2(lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_name_1139_; lean_object* v_name_1140_; uint8_t v___x_1141_; 
v_name_1139_ = lean_ctor_get(v___y_1137_, 0);
v_name_1140_ = lean_ctor_get(v___y_1138_, 0);
v___x_1141_ = l_Lean_Name_quickLt(v_name_1139_, v_name_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2___boxed(lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
uint8_t v_res_1144_; lean_object* v_r_1145_; 
v_res_1144_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2(v___y_1142_, v___y_1143_);
lean_dec_ref(v___y_1143_);
lean_dec_ref(v___y_1142_);
v_r_1145_ = lean_box(v_res_1144_);
return v_r_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0(lean_object* v_env_1146_, lean_object* v_as_1147_, size_t v_i_1148_, size_t v_stop_1149_, lean_object* v_b_1150_){
_start:
{
lean_object* v___y_1152_; uint8_t v___x_1156_; 
v___x_1156_ = lean_usize_dec_eq(v_i_1148_, v_stop_1149_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; lean_object* v_name_1158_; uint8_t v___x_1159_; 
v___x_1157_ = lean_array_uget_borrowed(v_as_1147_, v_i_1148_);
v_name_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc_ref(v_env_1146_);
v___x_1159_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_1146_, v_name_1158_);
if (v___x_1159_ == 0)
{
v___y_1152_ = v_b_1150_;
goto v___jp_1151_;
}
else
{
lean_object* v___x_1160_; 
lean_inc(v___x_1157_);
v___x_1160_ = lean_array_push(v_b_1150_, v___x_1157_);
v___y_1152_ = v___x_1160_;
goto v___jp_1151_;
}
}
else
{
lean_dec_ref(v_env_1146_);
return v_b_1150_;
}
v___jp_1151_:
{
size_t v___x_1153_; size_t v___x_1154_; 
v___x_1153_ = ((size_t)1ULL);
v___x_1154_ = lean_usize_add(v_i_1148_, v___x_1153_);
v_i_1148_ = v___x_1154_;
v_b_1150_ = v___y_1152_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0___boxed(lean_object* v_env_1161_, lean_object* v_as_1162_, lean_object* v_i_1163_, lean_object* v_stop_1164_, lean_object* v_b_1165_){
_start:
{
size_t v_i_boxed_1166_; size_t v_stop_boxed_1167_; lean_object* v_res_1168_; 
v_i_boxed_1166_ = lean_unbox_usize(v_i_1163_);
lean_dec(v_i_1163_);
v_stop_boxed_1167_ = lean_unbox_usize(v_stop_1164_);
lean_dec(v_stop_1164_);
v_res_1168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0(v_env_1161_, v_as_1162_, v_i_boxed_1166_, v_stop_boxed_1167_, v_b_1165_);
lean_dec_ref(v_as_1162_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0(lean_object* v_env_1169_, lean_object* v_as_1170_, lean_object* v_start_1171_, lean_object* v_stop_1172_){
_start:
{
lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1___closed__0));
v___x_1174_ = lean_nat_dec_lt(v_start_1171_, v_stop_1172_);
if (v___x_1174_ == 0)
{
lean_dec_ref(v_env_1169_);
return v___x_1173_;
}
else
{
lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = lean_array_get_size(v_as_1170_);
v___x_1176_ = lean_nat_dec_le(v_stop_1172_, v___x_1175_);
if (v___x_1176_ == 0)
{
uint8_t v___x_1177_; 
v___x_1177_ = lean_nat_dec_lt(v_start_1171_, v___x_1175_);
if (v___x_1177_ == 0)
{
lean_dec_ref(v_env_1169_);
return v___x_1173_;
}
else
{
size_t v___x_1178_; size_t v___x_1179_; lean_object* v___x_1180_; 
v___x_1178_ = lean_usize_of_nat(v_start_1171_);
v___x_1179_ = lean_usize_of_nat(v___x_1175_);
v___x_1180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0(v_env_1169_, v_as_1170_, v___x_1178_, v___x_1179_, v___x_1173_);
return v___x_1180_;
}
}
else
{
size_t v___x_1181_; size_t v___x_1182_; lean_object* v___x_1183_; 
v___x_1181_ = lean_usize_of_nat(v_start_1171_);
v___x_1182_ = lean_usize_of_nat(v_stop_1172_);
v___x_1183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0(v_env_1169_, v_as_1170_, v___x_1181_, v___x_1182_, v___x_1173_);
return v___x_1183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0___boxed(lean_object* v_env_1184_, lean_object* v_as_1185_, lean_object* v_start_1186_, lean_object* v_stop_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0(v_env_1184_, v_as_1185_, v_start_1186_, v_stop_1187_);
lean_dec(v_stop_1187_);
lean_dec(v_start_1186_);
lean_dec_ref(v_as_1185_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3(lean_object* v___f_1189_, lean_object* v_env_1190_, lean_object* v_s_1191_, uint8_t v_level_1192_){
_start:
{
lean_object* v_entries_1193_; uint8_t v___x_1194_; uint8_t v___x_1195_; 
v_entries_1193_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(v_s_1191_, v___f_1189_);
v___x_1194_ = 2;
v___x_1195_ = l_Lean_instDecidableEqOLeanLevel(v_level_1192_, v___x_1194_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v_entries_1198_; 
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = lean_array_get_size(v_entries_1193_);
v_entries_1198_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0(v_env_1190_, v_entries_1193_, v___x_1196_, v___x_1197_);
lean_dec_ref(v_entries_1193_);
return v_entries_1198_;
}
else
{
lean_dec_ref(v_env_1190_);
return v_entries_1193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3___boxed(lean_object* v___f_1199_, lean_object* v_env_1200_, lean_object* v_s_1201_, lean_object* v_level_1202_){
_start:
{
uint8_t v_level_boxed_1203_; lean_object* v_res_1204_; 
v_level_boxed_1203_ = lean_unbox(v_level_1202_);
v_res_1204_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3(v___f_1199_, v_env_1200_, v_s_1201_, v_level_boxed_1203_);
lean_dec_ref(v_s_1201_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__4(lean_object* v___x_1205_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1205_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__4___boxed(lean_object* v___x_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__4(v___x_1208_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__5(lean_object* v___x_1211_, lean_object* v_x_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1211_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__5___boxed(lean_object* v___x_1216_, lean_object* v_x_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__5(v___x_1216_, v_x_1217_, v___y_1218_);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v_x_1217_);
return v_res_1220_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4(void){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1226_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4, &l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4_once, _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4);
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
return v___x_1228_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6(void){
_start:
{
lean_object* v___x_1229_; lean_object* v___f_1230_; 
v___x_1229_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5, &l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5_once, _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5);
v___f_1230_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkSigDeclExt___lam__4___boxed), 2, 1);
lean_closure_set(v___f_1230_, 0, v___x_1229_);
return v___f_1230_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__7(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___f_1232_; 
v___x_1231_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5, &l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5_once, _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5);
v___f_1232_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkSigDeclExt___lam__5___boxed), 4, 1);
lean_closure_set(v___f_1232_, 0, v___x_1231_);
return v___f_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt(uint8_t v_phase_1233_, lean_object* v_name_1234_){
_start:
{
lean_object* v___f_1236_; lean_object* v___f_1237_; lean_object* v___f_1238_; lean_object* v___f_1239_; lean_object* v___f_1240_; uint8_t v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___f_1236_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__0));
v___f_1237_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__1));
v___f_1238_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__3));
v___f_1239_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6, &l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6_once, _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6);
v___f_1240_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__7, &l_Lean_Compiler_LCNF_mkSigDeclExt___closed__7_once, _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__7);
v___x_1241_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_1233_);
v___x_1242_ = lean_box(v___x_1241_);
v___x_1243_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___boxed), 3, 2);
lean_closure_set(v___x_1243_, 0, v___x_1242_);
lean_closure_set(v___x_1243_, 1, lean_box(0));
v___x_1244_ = lean_box(0);
v___x_1245_ = lean_box(v_phase_1233_);
v___x_1246_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___boxed), 6, 2);
lean_closure_set(v___x_1246_, 0, lean_box(0));
lean_closure_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
v___x_1248_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1248_, 0, v_name_1234_);
lean_ctor_set(v___x_1248_, 1, v___f_1239_);
lean_ctor_set(v___x_1248_, 2, v___f_1240_);
lean_ctor_set(v___x_1248_, 3, v___f_1236_);
lean_ctor_set(v___x_1248_, 4, v___f_1238_);
lean_ctor_set(v___x_1248_, 5, v___x_1243_);
lean_ctor_set(v___x_1248_, 6, v___x_1244_);
lean_ctor_set(v___x_1248_, 7, v___x_1247_);
v___x_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
lean_ctor_set(v___x_1249_, 1, v___f_1237_);
v___x_1250_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___boxed(lean_object* v_phase_1251_, lean_object* v_name_1252_, lean_object* v_a_1253_){
_start:
{
uint8_t v_phase_boxed_1254_; lean_object* v_res_1255_; 
v_phase_boxed_1254_ = lean_unbox(v_phase_1251_);
v_res_1255_ = l_Lean_Compiler_LCNF_mkSigDeclExt(v_phase_boxed_1254_, v_name_1252_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = 2;
v___x_1264_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_));
v___x_1265_ = l_Lean_Compiler_LCNF_mkSigDeclExt(v___x_1263_, v___x_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2____boxed(lean_object* v_a_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_();
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(lean_object* v_as_1268_, lean_object* v_k_1269_, lean_object* v_x_1270_, lean_object* v_x_1271_){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v_m_1274_; lean_object* v_a_1275_; uint8_t v___x_1276_; 
v___x_1272_ = lean_nat_add(v_x_1270_, v_x_1271_);
v___x_1273_ = lean_unsigned_to_nat(1u);
v_m_1274_ = lean_nat_shiftr(v___x_1272_, v___x_1273_);
lean_dec(v___x_1272_);
v_a_1275_ = lean_array_fget_borrowed(v_as_1268_, v_m_1274_);
v___x_1276_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__2(v_a_1275_, v_k_1269_);
if (v___x_1276_ == 0)
{
uint8_t v___x_1277_; 
lean_dec(v_x_1271_);
v___x_1277_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__2(v_k_1269_, v_a_1275_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; 
lean_dec(v_m_1274_);
lean_dec(v_x_1270_);
lean_inc(v_a_1275_);
v___x_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1278_, 0, v_a_1275_);
return v___x_1278_;
}
else
{
lean_object* v___x_1279_; uint8_t v___x_1280_; 
v___x_1279_ = lean_unsigned_to_nat(0u);
v___x_1280_ = lean_nat_dec_eq(v_m_1274_, v___x_1279_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1281_ = lean_nat_sub(v_m_1274_, v___x_1273_);
lean_dec(v_m_1274_);
v___x_1282_ = lean_nat_dec_lt(v___x_1281_, v_x_1270_);
if (v___x_1282_ == 0)
{
v_x_1271_ = v___x_1281_;
goto _start;
}
else
{
lean_object* v___x_1284_; 
lean_dec(v___x_1281_);
lean_dec(v_x_1270_);
v___x_1284_ = lean_box(0);
return v___x_1284_;
}
}
else
{
lean_object* v___x_1285_; 
lean_dec(v_m_1274_);
lean_dec(v_x_1270_);
v___x_1285_ = lean_box(0);
return v___x_1285_;
}
}
}
else
{
lean_object* v___x_1286_; uint8_t v___x_1287_; 
lean_dec(v_x_1270_);
v___x_1286_ = lean_nat_add(v_m_1274_, v___x_1273_);
lean_dec(v_m_1274_);
v___x_1287_ = lean_nat_dec_le(v___x_1286_, v_x_1271_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; 
lean_dec(v___x_1286_);
lean_dec(v_x_1271_);
v___x_1288_ = lean_box(0);
return v___x_1288_;
}
else
{
v_x_1270_ = v___x_1286_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg___boxed(lean_object* v_as_1290_, lean_object* v_k_1291_, lean_object* v_x_1292_, lean_object* v_x_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(v_as_1290_, v_k_1291_, v_x_1292_, v_x_1293_);
lean_dec_ref(v_k_1291_);
lean_dec_ref(v_as_1290_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1295_, lean_object* v_vals_1296_, lean_object* v_i_1297_, lean_object* v_k_1298_){
_start:
{
lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = lean_array_get_size(v_keys_1295_);
v___x_1300_ = lean_nat_dec_lt(v_i_1297_, v___x_1299_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; 
lean_dec(v_i_1297_);
v___x_1301_ = lean_box(0);
return v___x_1301_;
}
else
{
lean_object* v_k_x27_1302_; uint8_t v___x_1303_; 
v_k_x27_1302_ = lean_array_fget_borrowed(v_keys_1295_, v_i_1297_);
v___x_1303_ = lean_name_eq(v_k_1298_, v_k_x27_1302_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = lean_unsigned_to_nat(1u);
v___x_1305_ = lean_nat_add(v_i_1297_, v___x_1304_);
lean_dec(v_i_1297_);
v_i_1297_ = v___x_1305_;
goto _start;
}
else
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = lean_array_fget_borrowed(v_vals_1296_, v_i_1297_);
lean_dec(v_i_1297_);
lean_inc(v___x_1307_);
v___x_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
return v___x_1308_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1309_, lean_object* v_vals_1310_, lean_object* v_i_1311_, lean_object* v_k_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1309_, v_vals_1310_, v_i_1311_, v_k_1312_);
lean_dec(v_k_1312_);
lean_dec_ref(v_vals_1310_);
lean_dec_ref(v_keys_1309_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg(lean_object* v_x_1314_, size_t v_x_1315_, lean_object* v_x_1316_){
_start:
{
if (lean_obj_tag(v_x_1314_) == 0)
{
lean_object* v_es_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1338_; 
v_es_1317_ = lean_ctor_get(v_x_1314_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v_x_1314_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1319_ = v_x_1314_;
v_isShared_1320_ = v_isSharedCheck_1338_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_es_1317_);
lean_dec(v_x_1314_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1338_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; size_t v___x_1322_; size_t v___x_1323_; size_t v___x_1324_; lean_object* v_j_1325_; lean_object* v___x_1326_; 
v___x_1321_ = lean_box(2);
v___x_1322_ = ((size_t)5ULL);
v___x_1323_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1);
v___x_1324_ = lean_usize_land(v_x_1315_, v___x_1323_);
v_j_1325_ = lean_usize_to_nat(v___x_1324_);
v___x_1326_ = lean_array_get(v___x_1321_, v_es_1317_, v_j_1325_);
lean_dec(v_j_1325_);
lean_dec_ref(v_es_1317_);
switch(lean_obj_tag(v___x_1326_))
{
case 0:
{
lean_object* v_key_1327_; lean_object* v_val_1328_; uint8_t v___x_1329_; 
v_key_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_key_1327_);
v_val_1328_ = lean_ctor_get(v___x_1326_, 1);
lean_inc(v_val_1328_);
lean_dec_ref(v___x_1326_);
v___x_1329_ = lean_name_eq(v_x_1316_, v_key_1327_);
lean_dec(v_key_1327_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; 
lean_dec(v_val_1328_);
lean_del_object(v___x_1319_);
v___x_1330_ = lean_box(0);
return v___x_1330_;
}
else
{
lean_object* v___x_1332_; 
if (v_isShared_1320_ == 0)
{
lean_ctor_set_tag(v___x_1319_, 1);
lean_ctor_set(v___x_1319_, 0, v_val_1328_);
v___x_1332_ = v___x_1319_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_val_1328_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
case 1:
{
lean_object* v_node_1334_; size_t v___x_1335_; 
lean_del_object(v___x_1319_);
v_node_1334_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_node_1334_);
lean_dec_ref(v___x_1326_);
v___x_1335_ = lean_usize_shift_right(v_x_1315_, v___x_1322_);
v_x_1314_ = v_node_1334_;
v_x_1315_ = v___x_1335_;
goto _start;
}
default: 
{
lean_object* v___x_1337_; 
lean_del_object(v___x_1319_);
v___x_1337_ = lean_box(0);
return v___x_1337_;
}
}
}
}
else
{
lean_object* v_ks_1339_; lean_object* v_vs_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v_ks_1339_ = lean_ctor_get(v_x_1314_, 0);
lean_inc_ref(v_ks_1339_);
v_vs_1340_ = lean_ctor_get(v_x_1314_, 1);
lean_inc_ref(v_vs_1340_);
lean_dec_ref(v_x_1314_);
v___x_1341_ = lean_unsigned_to_nat(0u);
v___x_1342_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1339_, v_vs_1340_, v___x_1341_, v_x_1316_);
lean_dec_ref(v_vs_1340_);
lean_dec_ref(v_ks_1339_);
return v___x_1342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1343_, lean_object* v_x_1344_, lean_object* v_x_1345_){
_start:
{
size_t v_x_429__boxed_1346_; lean_object* v_res_1347_; 
v_x_429__boxed_1346_ = lean_unbox_usize(v_x_1344_);
lean_dec(v_x_1344_);
v_res_1347_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg(v_x_1343_, v_x_429__boxed_1346_, v_x_1345_);
lean_dec(v_x_1345_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(lean_object* v_x_1348_, lean_object* v_x_1349_){
_start:
{
uint64_t v___y_1351_; 
if (lean_obj_tag(v_x_1349_) == 0)
{
uint64_t v___x_1354_; 
v___x_1354_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0);
v___y_1351_ = v___x_1354_;
goto v___jp_1350_;
}
else
{
uint64_t v_hash_1355_; 
v_hash_1355_ = lean_ctor_get_uint64(v_x_1349_, sizeof(void*)*2);
v___y_1351_ = v_hash_1355_;
goto v___jp_1350_;
}
v___jp_1350_:
{
size_t v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = lean_uint64_to_usize(v___y_1351_);
v___x_1353_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg(v_x_1348_, v___x_1352_, v_x_1349_);
return v___x_1353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg___boxed(lean_object* v_x_1356_, lean_object* v_x_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v_x_1356_, v_x_1357_);
lean_dec(v_x_1357_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclCore_x3f(uint8_t v_pu_1359_, lean_object* v_env_1360_, lean_object* v_ext_1361_, lean_object* v_declName_1362_){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1370_; 
v___x_1363_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__2, &l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__2);
v___x_1370_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1360_, v_declName_1362_);
if (lean_obj_tag(v___x_1370_) == 0)
{
goto v___jp_1364_;
}
else
{
lean_object* v_val_1371_; lean_object* v_tmpDecl_1406_; lean_object* v_toSignature_1407_; lean_object* v_value_1408_; uint8_t v_recursive_1409_; lean_object* v_inlineAttr_x3f_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1437_; 
v_val_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc(v_val_1371_);
lean_dec_ref(v___x_1370_);
v_tmpDecl_1406_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default(v_pu_1359_);
v_toSignature_1407_ = lean_ctor_get(v_tmpDecl_1406_, 0);
v_value_1408_ = lean_ctor_get(v_tmpDecl_1406_, 1);
v_recursive_1409_ = lean_ctor_get_uint8(v_tmpDecl_1406_, sizeof(void*)*3);
v_inlineAttr_x3f_1410_ = lean_ctor_get(v_tmpDecl_1406_, 2);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_tmpDecl_1406_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1412_ = v_tmpDecl_1406_;
v_isShared_1413_ = v_isSharedCheck_1437_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_inlineAttr_x3f_1410_);
lean_inc(v_value_1408_);
lean_inc(v_toSignature_1407_);
lean_dec(v_tmpDecl_1406_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1437_;
goto v_resetjp_1411_;
}
v___jp_1372_:
{
lean_object* v_tmpDecl_1373_; lean_object* v_toSignature_1374_; lean_object* v_value_1375_; uint8_t v_recursive_1376_; lean_object* v_inlineAttr_x3f_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1405_; 
v_tmpDecl_1373_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default(v_pu_1359_);
v_toSignature_1374_ = lean_ctor_get(v_tmpDecl_1373_, 0);
v_value_1375_ = lean_ctor_get(v_tmpDecl_1373_, 1);
v_recursive_1376_ = lean_ctor_get_uint8(v_tmpDecl_1373_, sizeof(void*)*3);
v_inlineAttr_x3f_1377_ = lean_ctor_get(v_tmpDecl_1373_, 2);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_tmpDecl_1373_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1379_ = v_tmpDecl_1373_;
v_isShared_1380_ = v_isSharedCheck_1405_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_inlineAttr_x3f_1377_);
lean_inc(v_value_1375_);
lean_inc(v_toSignature_1374_);
lean_dec(v_tmpDecl_1373_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1405_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v_levelParams_1381_; lean_object* v_type_1382_; lean_object* v_params_1383_; uint8_t v_safe_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1403_; 
v_levelParams_1381_ = lean_ctor_get(v_toSignature_1374_, 1);
v_type_1382_ = lean_ctor_get(v_toSignature_1374_, 2);
v_params_1383_ = lean_ctor_get(v_toSignature_1374_, 3);
v_safe_1384_ = lean_ctor_get_uint8(v_toSignature_1374_, sizeof(void*)*4);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_toSignature_1374_);
if (v_isSharedCheck_1403_ == 0)
{
lean_object* v_unused_1404_; 
v_unused_1404_ = lean_ctor_get(v_toSignature_1374_, 0);
lean_dec(v_unused_1404_);
v___x_1386_ = v_toSignature_1374_;
v_isShared_1387_ = v_isSharedCheck_1403_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_params_1383_);
lean_inc(v_type_1382_);
lean_inc(v_levelParams_1381_);
lean_dec(v_toSignature_1374_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1403_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
uint8_t v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___x_1388_ = 0;
v___x_1389_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1363_, v_ext_1361_, v_env_1360_, v_val_1371_, v___x_1388_);
lean_dec(v_val_1371_);
v___x_1390_ = lean_unsigned_to_nat(0u);
v___x_1391_ = lean_array_get_size(v___x_1389_);
v___x_1392_ = lean_nat_dec_lt(v___x_1390_, v___x_1391_);
if (v___x_1392_ == 0)
{
lean_dec_ref(v___x_1389_);
lean_del_object(v___x_1386_);
lean_dec_ref(v_params_1383_);
lean_dec_ref(v_type_1382_);
lean_dec(v_levelParams_1381_);
lean_del_object(v___x_1379_);
lean_dec(v_inlineAttr_x3f_1377_);
lean_dec_ref(v_value_1375_);
goto v___jp_1364_;
}
else
{
lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_1393_ = lean_unsigned_to_nat(1u);
v___x_1394_ = lean_nat_sub(v___x_1391_, v___x_1393_);
v___x_1395_ = lean_nat_dec_le(v___x_1390_, v___x_1394_);
if (v___x_1395_ == 0)
{
lean_dec(v___x_1394_);
lean_dec_ref(v___x_1389_);
lean_del_object(v___x_1386_);
lean_dec_ref(v_params_1383_);
lean_dec_ref(v_type_1382_);
lean_dec(v_levelParams_1381_);
lean_del_object(v___x_1379_);
lean_dec(v_inlineAttr_x3f_1377_);
lean_dec_ref(v_value_1375_);
goto v___jp_1364_;
}
else
{
lean_object* v___x_1397_; 
lean_inc(v_declName_1362_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v_declName_1362_);
v___x_1397_ = v___x_1386_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_declName_1362_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_levelParams_1381_);
lean_ctor_set(v_reuseFailAlloc_1402_, 2, v_type_1382_);
lean_ctor_set(v_reuseFailAlloc_1402_, 3, v_params_1383_);
lean_ctor_set_uint8(v_reuseFailAlloc_1402_, sizeof(void*)*4, v_safe_1384_);
v___x_1397_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
lean_object* v_tmpDecl_1399_; 
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1397_);
v_tmpDecl_1399_ = v___x_1379_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_value_1375_);
lean_ctor_set(v_reuseFailAlloc_1401_, 2, v_inlineAttr_x3f_1377_);
lean_ctor_set_uint8(v_reuseFailAlloc_1401_, sizeof(void*)*3, v_recursive_1376_);
v_tmpDecl_1399_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(v___x_1389_, v_tmpDecl_1399_, v___x_1390_, v___x_1394_);
lean_dec_ref(v_tmpDecl_1399_);
lean_dec_ref(v___x_1389_);
if (lean_obj_tag(v___x_1400_) == 0)
{
goto v___jp_1364_;
}
else
{
lean_dec(v_declName_1362_);
lean_dec_ref(v_env_1360_);
return v___x_1400_;
}
}
}
}
}
}
}
}
v_resetjp_1411_:
{
lean_object* v_levelParams_1414_; lean_object* v_type_1415_; lean_object* v_params_1416_; uint8_t v_safe_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1435_; 
v_levelParams_1414_ = lean_ctor_get(v_toSignature_1407_, 1);
v_type_1415_ = lean_ctor_get(v_toSignature_1407_, 2);
v_params_1416_ = lean_ctor_get(v_toSignature_1407_, 3);
v_safe_1417_ = lean_ctor_get_uint8(v_toSignature_1407_, sizeof(void*)*4);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_toSignature_1407_);
if (v_isSharedCheck_1435_ == 0)
{
lean_object* v_unused_1436_; 
v_unused_1436_ = lean_ctor_get(v_toSignature_1407_, 0);
lean_dec(v_unused_1436_);
v___x_1419_ = v_toSignature_1407_;
v_isShared_1420_ = v_isSharedCheck_1435_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_params_1416_);
lean_inc(v_type_1415_);
lean_inc(v_levelParams_1414_);
lean_dec(v_toSignature_1407_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1435_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1421_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_1363_, v_ext_1361_, v_env_1360_, v_val_1371_);
v___x_1422_ = lean_unsigned_to_nat(0u);
v___x_1423_ = lean_array_get_size(v___x_1421_);
v___x_1424_ = lean_nat_dec_lt(v___x_1422_, v___x_1423_);
if (v___x_1424_ == 0)
{
lean_dec_ref(v___x_1421_);
lean_del_object(v___x_1419_);
lean_dec_ref(v_params_1416_);
lean_dec_ref(v_type_1415_);
lean_dec(v_levelParams_1414_);
lean_del_object(v___x_1412_);
lean_dec(v_inlineAttr_x3f_1410_);
lean_dec_ref(v_value_1408_);
goto v___jp_1372_;
}
else
{
lean_object* v___x_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
v___x_1425_ = lean_unsigned_to_nat(1u);
v___x_1426_ = lean_nat_sub(v___x_1423_, v___x_1425_);
v___x_1427_ = lean_nat_dec_le(v___x_1422_, v___x_1426_);
if (v___x_1427_ == 0)
{
lean_dec(v___x_1426_);
lean_dec_ref(v___x_1421_);
lean_del_object(v___x_1419_);
lean_dec_ref(v_params_1416_);
lean_dec_ref(v_type_1415_);
lean_dec(v_levelParams_1414_);
lean_del_object(v___x_1412_);
lean_dec(v_inlineAttr_x3f_1410_);
lean_dec_ref(v_value_1408_);
goto v___jp_1372_;
}
else
{
lean_object* v___x_1429_; 
lean_inc(v_declName_1362_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v_declName_1362_);
v___x_1429_ = v___x_1419_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_declName_1362_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_levelParams_1414_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v_type_1415_);
lean_ctor_set(v_reuseFailAlloc_1434_, 3, v_params_1416_);
lean_ctor_set_uint8(v_reuseFailAlloc_1434_, sizeof(void*)*4, v_safe_1417_);
v___x_1429_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v_tmpDecl_1431_; 
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 0, v___x_1429_);
v_tmpDecl_1431_ = v___x_1412_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v_value_1408_);
lean_ctor_set(v_reuseFailAlloc_1433_, 2, v_inlineAttr_x3f_1410_);
lean_ctor_set_uint8(v_reuseFailAlloc_1433_, sizeof(void*)*3, v_recursive_1409_);
v_tmpDecl_1431_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(v___x_1421_, v_tmpDecl_1431_, v___x_1422_, v___x_1426_);
lean_dec_ref(v_tmpDecl_1431_);
lean_dec_ref(v___x_1421_);
if (lean_obj_tag(v___x_1432_) == 0)
{
goto v___jp_1372_;
}
else
{
lean_dec(v_val_1371_);
lean_dec(v_declName_1362_);
lean_dec_ref(v_env_1360_);
return v___x_1432_;
}
}
}
}
}
}
}
}
v___jp_1364_:
{
lean_object* v_toEnvExtension_1365_; lean_object* v_asyncMode_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v_toEnvExtension_1365_ = lean_ctor_get(v_ext_1361_, 0);
v_asyncMode_1366_ = lean_ctor_get(v_toEnvExtension_1365_, 2);
v___x_1367_ = lean_box(0);
v___x_1368_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1363_, v_ext_1361_, v_env_1360_, v_asyncMode_1366_, v___x_1367_);
v___x_1369_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_1368_, v_declName_1362_);
lean_dec(v_declName_1362_);
return v___x_1369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclCore_x3f___boxed(lean_object* v_pu_1438_, lean_object* v_env_1439_, lean_object* v_ext_1440_, lean_object* v_declName_1441_){
_start:
{
uint8_t v_pu_boxed_1442_; lean_object* v_res_1443_; 
v_pu_boxed_1442_ = lean_unbox(v_pu_1438_);
v_res_1443_ = l_Lean_Compiler_LCNF_getDeclCore_x3f(v_pu_boxed_1442_, v_env_1439_, v_ext_1440_, v_declName_1441_);
lean_dec_ref(v_ext_1440_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0(lean_object* v_00_u03b2_1444_, lean_object* v_x_1445_, lean_object* v_x_1446_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v_x_1445_, v_x_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___boxed(lean_object* v_00_u03b2_1448_, lean_object* v_x_1449_, lean_object* v_x_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0(v_00_u03b2_1448_, v_x_1449_, v_x_1450_);
lean_dec(v_x_1450_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1(lean_object* v_as_1452_, lean_object* v_k_1453_, lean_object* v_x_1454_, lean_object* v_x_1455_, lean_object* v_x_1456_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(v_as_1452_, v_k_1453_, v_x_1454_, v_x_1455_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___boxed(lean_object* v_as_1458_, lean_object* v_k_1459_, lean_object* v_x_1460_, lean_object* v_x_1461_, lean_object* v_x_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1(v_as_1458_, v_k_1459_, v_x_1460_, v_x_1461_, v_x_1462_);
lean_dec_ref(v_k_1459_);
lean_dec_ref(v_as_1458_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1464_, lean_object* v_x_1465_, size_t v_x_1466_, lean_object* v_x_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg(v_x_1465_, v_x_1466_, v_x_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1469_, lean_object* v_x_1470_, lean_object* v_x_1471_, lean_object* v_x_1472_){
_start:
{
size_t v_x_643__boxed_1473_; lean_object* v_res_1474_; 
v_x_643__boxed_1473_ = lean_unbox_usize(v_x_1471_);
lean_dec(v_x_1471_);
v_res_1474_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0(v_00_u03b2_1469_, v_x_1470_, v_x_643__boxed_1473_, v_x_1472_);
lean_dec(v_x_1472_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1475_, lean_object* v_keys_1476_, lean_object* v_vals_1477_, lean_object* v_heq_1478_, lean_object* v_i_1479_, lean_object* v_k_1480_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1476_, v_vals_1477_, v_i_1479_, v_k_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1482_, lean_object* v_keys_1483_, lean_object* v_vals_1484_, lean_object* v_heq_1485_, lean_object* v_i_1486_, lean_object* v_k_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1482_, v_keys_1483_, v_vals_1484_, v_heq_1485_, v_i_1486_, v_k_1487_);
lean_dec(v_k_1487_);
lean_dec_ref(v_vals_1484_);
lean_dec_ref(v_keys_1483_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(lean_object* v_as_1489_, lean_object* v_k_1490_, lean_object* v_x_1491_, lean_object* v_x_1492_){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v_m_1495_; lean_object* v_a_1496_; uint8_t v___x_1497_; 
v___x_1493_ = lean_nat_add(v_x_1491_, v_x_1492_);
v___x_1494_ = lean_unsigned_to_nat(1u);
v_m_1495_ = lean_nat_shiftr(v___x_1493_, v___x_1494_);
lean_dec(v___x_1493_);
v_a_1496_ = lean_array_fget_borrowed(v_as_1489_, v_m_1495_);
v___x_1497_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2(v_a_1496_, v_k_1490_);
if (v___x_1497_ == 0)
{
uint8_t v___x_1498_; 
lean_dec(v_x_1492_);
v___x_1498_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2(v_k_1490_, v_a_1496_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; 
lean_dec(v_m_1495_);
lean_dec(v_x_1491_);
lean_inc(v_a_1496_);
v___x_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1499_, 0, v_a_1496_);
return v___x_1499_;
}
else
{
lean_object* v___x_1500_; uint8_t v___x_1501_; 
v___x_1500_ = lean_unsigned_to_nat(0u);
v___x_1501_ = lean_nat_dec_eq(v_m_1495_, v___x_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1502_ = lean_nat_sub(v_m_1495_, v___x_1494_);
lean_dec(v_m_1495_);
v___x_1503_ = lean_nat_dec_lt(v___x_1502_, v_x_1491_);
if (v___x_1503_ == 0)
{
v_x_1492_ = v___x_1502_;
goto _start;
}
else
{
lean_object* v___x_1505_; 
lean_dec(v___x_1502_);
lean_dec(v_x_1491_);
v___x_1505_ = lean_box(0);
return v___x_1505_;
}
}
else
{
lean_object* v___x_1506_; 
lean_dec(v_m_1495_);
lean_dec(v_x_1491_);
v___x_1506_ = lean_box(0);
return v___x_1506_;
}
}
}
else
{
lean_object* v___x_1507_; uint8_t v___x_1508_; 
lean_dec(v_x_1491_);
v___x_1507_ = lean_nat_add(v_m_1495_, v___x_1494_);
lean_dec(v_m_1495_);
v___x_1508_ = lean_nat_dec_le(v___x_1507_, v_x_1492_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; 
lean_dec(v___x_1507_);
lean_dec(v_x_1492_);
v___x_1509_ = lean_box(0);
return v___x_1509_;
}
else
{
v_x_1491_ = v___x_1507_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg___boxed(lean_object* v_as_1511_, lean_object* v_k_1512_, lean_object* v_x_1513_, lean_object* v_x_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(v_as_1511_, v_k_1512_, v_x_1513_, v_x_1514_);
lean_dec_ref(v_k_1512_);
lean_dec_ref(v_as_1511_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSigCore_x3f(uint8_t v_pu_1516_, lean_object* v_env_1517_, lean_object* v_ext_1518_, lean_object* v_declName_1519_){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1527_; 
v___x_1520_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedSigExt___closed__0, &l_Lean_Compiler_LCNF_instInhabitedSigExt___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___closed__0);
v___x_1527_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1517_, v_declName_1519_);
if (lean_obj_tag(v___x_1527_) == 0)
{
goto v___jp_1521_;
}
else
{
lean_object* v_val_1528_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; uint8_t v___x_1555_; 
v_val_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_val_1528_);
lean_dec_ref(v___x_1527_);
v___x_1552_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_1520_, v_ext_1518_, v_env_1517_, v_val_1528_);
v___x_1553_ = lean_unsigned_to_nat(0u);
v___x_1554_ = lean_array_get_size(v___x_1552_);
v___x_1555_ = lean_nat_dec_lt(v___x_1553_, v___x_1554_);
if (v___x_1555_ == 0)
{
lean_dec_ref(v___x_1552_);
goto v___jp_1529_;
}
else
{
lean_object* v_tmpSig_1556_; lean_object* v_levelParams_1557_; lean_object* v_type_1558_; lean_object* v_params_1559_; uint8_t v_safe_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1571_; 
v_tmpSig_1556_ = l_Lean_Compiler_LCNF_instInhabitedSignature_default(v_pu_1516_);
v_levelParams_1557_ = lean_ctor_get(v_tmpSig_1556_, 1);
v_type_1558_ = lean_ctor_get(v_tmpSig_1556_, 2);
v_params_1559_ = lean_ctor_get(v_tmpSig_1556_, 3);
v_safe_1560_ = lean_ctor_get_uint8(v_tmpSig_1556_, sizeof(void*)*4);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_tmpSig_1556_);
if (v_isSharedCheck_1571_ == 0)
{
lean_object* v_unused_1572_; 
v_unused_1572_ = lean_ctor_get(v_tmpSig_1556_, 0);
lean_dec(v_unused_1572_);
v___x_1562_ = v_tmpSig_1556_;
v_isShared_1563_ = v_isSharedCheck_1571_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_params_1559_);
lean_inc(v_type_1558_);
lean_inc(v_levelParams_1557_);
lean_dec(v_tmpSig_1556_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1571_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; 
v___x_1564_ = lean_unsigned_to_nat(1u);
v___x_1565_ = lean_nat_sub(v___x_1554_, v___x_1564_);
v___x_1566_ = lean_nat_dec_le(v___x_1553_, v___x_1565_);
if (v___x_1566_ == 0)
{
lean_dec(v___x_1565_);
lean_del_object(v___x_1562_);
lean_dec_ref(v_params_1559_);
lean_dec_ref(v_type_1558_);
lean_dec(v_levelParams_1557_);
lean_dec_ref(v___x_1552_);
goto v___jp_1529_;
}
else
{
lean_object* v_tmpSig_1568_; 
lean_inc(v_declName_1519_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v_declName_1519_);
v_tmpSig_1568_ = v___x_1562_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_declName_1519_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_levelParams_1557_);
lean_ctor_set(v_reuseFailAlloc_1570_, 2, v_type_1558_);
lean_ctor_set(v_reuseFailAlloc_1570_, 3, v_params_1559_);
lean_ctor_set_uint8(v_reuseFailAlloc_1570_, sizeof(void*)*4, v_safe_1560_);
v_tmpSig_1568_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(v___x_1552_, v_tmpSig_1568_, v___x_1553_, v___x_1565_);
lean_dec_ref(v_tmpSig_1568_);
lean_dec_ref(v___x_1552_);
if (lean_obj_tag(v___x_1569_) == 0)
{
goto v___jp_1529_;
}
else
{
lean_dec(v_val_1528_);
lean_dec(v_declName_1519_);
lean_dec_ref(v_env_1517_);
return v___x_1569_;
}
}
}
}
}
v___jp_1529_:
{
uint8_t v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1530_ = 0;
v___x_1531_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1520_, v_ext_1518_, v_env_1517_, v_val_1528_, v___x_1530_);
lean_dec(v_val_1528_);
v___x_1532_ = lean_unsigned_to_nat(0u);
v___x_1533_ = lean_array_get_size(v___x_1531_);
v___x_1534_ = lean_nat_dec_lt(v___x_1532_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_dec_ref(v___x_1531_);
goto v___jp_1521_;
}
else
{
lean_object* v_tmpSig_1535_; lean_object* v_levelParams_1536_; lean_object* v_type_1537_; lean_object* v_params_1538_; uint8_t v_safe_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1550_; 
v_tmpSig_1535_ = l_Lean_Compiler_LCNF_instInhabitedSignature_default(v_pu_1516_);
v_levelParams_1536_ = lean_ctor_get(v_tmpSig_1535_, 1);
v_type_1537_ = lean_ctor_get(v_tmpSig_1535_, 2);
v_params_1538_ = lean_ctor_get(v_tmpSig_1535_, 3);
v_safe_1539_ = lean_ctor_get_uint8(v_tmpSig_1535_, sizeof(void*)*4);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_tmpSig_1535_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; 
v_unused_1551_ = lean_ctor_get(v_tmpSig_1535_, 0);
lean_dec(v_unused_1551_);
v___x_1541_ = v_tmpSig_1535_;
v_isShared_1542_ = v_isSharedCheck_1550_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_params_1538_);
lean_inc(v_type_1537_);
lean_inc(v_levelParams_1536_);
lean_dec(v_tmpSig_1535_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1550_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; 
v___x_1543_ = lean_unsigned_to_nat(1u);
v___x_1544_ = lean_nat_sub(v___x_1533_, v___x_1543_);
v___x_1545_ = lean_nat_dec_le(v___x_1532_, v___x_1544_);
if (v___x_1545_ == 0)
{
lean_dec(v___x_1544_);
lean_del_object(v___x_1541_);
lean_dec_ref(v_params_1538_);
lean_dec_ref(v_type_1537_);
lean_dec(v_levelParams_1536_);
lean_dec_ref(v___x_1531_);
goto v___jp_1521_;
}
else
{
lean_object* v_tmpSig_1547_; 
lean_inc(v_declName_1519_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v_declName_1519_);
v_tmpSig_1547_ = v___x_1541_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_declName_1519_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_levelParams_1536_);
lean_ctor_set(v_reuseFailAlloc_1549_, 2, v_type_1537_);
lean_ctor_set(v_reuseFailAlloc_1549_, 3, v_params_1538_);
lean_ctor_set_uint8(v_reuseFailAlloc_1549_, sizeof(void*)*4, v_safe_1539_);
v_tmpSig_1547_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(v___x_1531_, v_tmpSig_1547_, v___x_1532_, v___x_1544_);
lean_dec_ref(v_tmpSig_1547_);
lean_dec_ref(v___x_1531_);
if (lean_obj_tag(v___x_1548_) == 0)
{
goto v___jp_1521_;
}
else
{
lean_dec(v_declName_1519_);
lean_dec_ref(v_env_1517_);
return v___x_1548_;
}
}
}
}
}
}
}
v___jp_1521_:
{
lean_object* v_toEnvExtension_1522_; lean_object* v_asyncMode_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_toEnvExtension_1522_ = lean_ctor_get(v_ext_1518_, 0);
v_asyncMode_1523_ = lean_ctor_get(v_toEnvExtension_1522_, 2);
v___x_1524_ = lean_box(0);
v___x_1525_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1520_, v_ext_1518_, v_env_1517_, v_asyncMode_1523_, v___x_1524_);
v___x_1526_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_1525_, v_declName_1519_);
lean_dec(v_declName_1519_);
return v___x_1526_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSigCore_x3f___boxed(lean_object* v_pu_1573_, lean_object* v_env_1574_, lean_object* v_ext_1575_, lean_object* v_declName_1576_){
_start:
{
uint8_t v_pu_boxed_1577_; lean_object* v_res_1578_; 
v_pu_boxed_1577_ = lean_unbox(v_pu_1573_);
v_res_1578_ = l_Lean_Compiler_LCNF_getSigCore_x3f(v_pu_boxed_1577_, v_env_1574_, v_ext_1575_, v_declName_1576_);
lean_dec_ref(v_ext_1575_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0(lean_object* v_as_1579_, lean_object* v_k_1580_, lean_object* v_x_1581_, lean_object* v_x_1582_, lean_object* v_x_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(v_as_1579_, v_k_1580_, v_x_1581_, v_x_1582_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___boxed(lean_object* v_as_1585_, lean_object* v_k_1586_, lean_object* v_x_1587_, lean_object* v_x_1588_, lean_object* v_x_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0(v_as_1585_, v_k_1586_, v_x_1587_, v_x_1588_, v_x_1589_);
lean_dec_ref(v_k_1586_);
lean_dec_ref(v_as_1585_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg(lean_object* v_declName_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v___x_1594_; lean_object* v_env_1595_; uint8_t v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1594_ = lean_st_ref_get(v_a_1592_);
v_env_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc_ref(v_env_1595_);
lean_dec(v___x_1594_);
v___x_1596_ = 0;
v___x_1597_ = l_Lean_Compiler_LCNF_baseExt;
v___x_1598_ = l_Lean_Compiler_LCNF_getDeclCore_x3f(v___x_1596_, v_env_1595_, v___x_1597_, v_declName_1591_);
v___x_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg___boxed(lean_object* v_declName_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg(v_declName_1600_, v_a_1601_);
lean_dec(v_a_1601_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBaseDecl_x3f(lean_object* v_declName_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg(v_declName_1604_, v_a_1606_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBaseDecl_x3f___boxed(lean_object* v_declName_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_Compiler_LCNF_getBaseDecl_x3f(v_declName_1609_, v_a_1610_, v_a_1611_);
lean_dec(v_a_1611_);
lean_dec_ref(v_a_1610_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(lean_object* v_declName_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v___x_1617_; lean_object* v_env_1618_; uint8_t v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1617_ = lean_st_ref_get(v_a_1615_);
v_env_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc_ref(v_env_1618_);
lean_dec(v___x_1617_);
v___x_1619_ = 0;
v___x_1620_ = l_Lean_Compiler_LCNF_monoExt;
v___x_1621_ = l_Lean_Compiler_LCNF_getDeclCore_x3f(v___x_1619_, v_env_1618_, v___x_1620_, v_declName_1614_);
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg___boxed(lean_object* v_declName_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_1623_, v_a_1624_);
lean_dec(v_a_1624_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f(lean_object* v_declName_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_1627_, v_a_1629_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___boxed(lean_object* v_declName_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f(v_declName_1632_, v_a_1633_, v_a_1634_);
lean_dec(v_a_1634_);
lean_dec_ref(v_a_1633_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg(lean_object* v_declName_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v___x_1640_; lean_object* v_env_1641_; lean_object* v___x_1642_; lean_object* v_asyncMode_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1640_ = lean_st_ref_get(v_a_1638_);
v_env_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc_ref(v_env_1641_);
lean_dec(v___x_1640_);
v___x_1642_ = l_Lean_Compiler_LCNF_impureExt;
v_asyncMode_1643_ = lean_ctor_get(v___x_1642_, 2);
lean_inc(v_asyncMode_1643_);
v___x_1644_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__2, &l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__2);
v___x_1645_ = lean_box(0);
v___x_1646_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1644_, v___x_1642_, v_env_1641_, v_asyncMode_1643_, v___x_1645_);
lean_dec(v_asyncMode_1643_);
v___x_1647_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_1646_, v_declName_1637_);
v___x_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg___boxed(lean_object* v_declName_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg(v_declName_1649_, v_a_1650_);
lean_dec(v_a_1650_);
lean_dec(v_declName_1649_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f(lean_object* v_declName_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg(v_declName_1653_, v_a_1655_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___boxed(lean_object* v_declName_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f(v_declName_1658_, v_a_1659_, v_a_1660_);
lean_dec(v_a_1660_);
lean_dec_ref(v_a_1659_);
lean_dec(v_declName_1658_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__1(size_t v_sz_1663_, size_t v_i_1664_, lean_object* v_bs_1665_){
_start:
{
uint8_t v___x_1666_; 
v___x_1666_ = lean_usize_dec_lt(v_i_1664_, v_sz_1663_);
if (v___x_1666_ == 0)
{
return v_bs_1665_;
}
else
{
lean_object* v_v_1667_; lean_object* v_fst_1668_; lean_object* v___x_1669_; lean_object* v_bs_x27_1670_; size_t v___x_1671_; size_t v___x_1672_; lean_object* v___x_1673_; 
v_v_1667_ = lean_array_uget_borrowed(v_bs_1665_, v_i_1664_);
v_fst_1668_ = lean_ctor_get(v_v_1667_, 0);
lean_inc(v_fst_1668_);
v___x_1669_ = lean_unsigned_to_nat(0u);
v_bs_x27_1670_ = lean_array_uset(v_bs_1665_, v_i_1664_, v___x_1669_);
v___x_1671_ = ((size_t)1ULL);
v___x_1672_ = lean_usize_add(v_i_1664_, v___x_1671_);
v___x_1673_ = lean_array_uset(v_bs_x27_1670_, v_i_1664_, v_fst_1668_);
v_i_1664_ = v___x_1672_;
v_bs_1665_ = v___x_1673_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__1___boxed(lean_object* v_sz_1675_, lean_object* v_i_1676_, lean_object* v_bs_1677_){
_start:
{
size_t v_sz_boxed_1678_; size_t v_i_boxed_1679_; lean_object* v_res_1680_; 
v_sz_boxed_1678_ = lean_unbox_usize(v_sz_1675_);
lean_dec(v_sz_1675_);
v_i_boxed_1679_ = lean_unbox_usize(v_i_1676_);
lean_dec(v_i_1676_);
v_res_1680_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__1(v_sz_boxed_1678_, v_i_boxed_1679_, v_bs_1677_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___lam__0(lean_object* v_ps_1681_, lean_object* v_k_1682_, lean_object* v_v_1683_){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1684_, 0, v_k_1682_);
lean_ctor_set(v___x_1684_, 1, v_v_1683_);
v___x_1685_ = lean_array_push(v_ps_1681_, v___x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg(lean_object* v_m_1689_){
_start:
{
lean_object* v___f_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___f_1690_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__0));
v___x_1691_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__1));
v___x_1692_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_m_1689_, v___f_1690_, v___x_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___boxed(lean_object* v_m_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg(v_m_1693_);
lean_dec_ref(v_m_1693_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecls___redArg(lean_object* v_a_1695_){
_start:
{
lean_object* v___x_1697_; lean_object* v_env_1698_; lean_object* v___x_1699_; lean_object* v_asyncMode_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; size_t v_sz_1705_; size_t v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1697_ = lean_st_ref_get(v_a_1695_);
v_env_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc_ref(v_env_1698_);
lean_dec(v___x_1697_);
v___x_1699_ = l_Lean_Compiler_LCNF_impureExt;
v_asyncMode_1700_ = lean_ctor_get(v___x_1699_, 2);
lean_inc(v_asyncMode_1700_);
v___x_1701_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__2, &l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__2);
v___x_1702_ = lean_box(0);
v___x_1703_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1701_, v___x_1699_, v_env_1698_, v_asyncMode_1700_, v___x_1702_);
lean_dec(v_asyncMode_1700_);
v___x_1704_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg(v___x_1703_);
lean_dec(v___x_1703_);
v_sz_1705_ = lean_array_size(v___x_1704_);
v___x_1706_ = ((size_t)0ULL);
v___x_1707_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__1(v_sz_1705_, v___x_1706_, v___x_1704_);
v___x_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecls___redArg___boxed(lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_Compiler_LCNF_getLocalImpureDecls___redArg(v_a_1709_);
lean_dec(v_a_1709_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecls(lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Lean_Compiler_LCNF_getLocalImpureDecls___redArg(v_a_1713_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecls___boxed(lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Lean_Compiler_LCNF_getLocalImpureDecls(v_a_1716_, v_a_1717_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0(lean_object* v_00_u03b2_1720_, lean_object* v_m_1721_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg(v_m_1721_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___boxed(lean_object* v_00_u03b2_1723_, lean_object* v_m_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0(v_00_u03b2_1723_, v_m_1724_);
lean_dec_ref(v_m_1724_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object* v_declName_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v___x_1729_; lean_object* v_env_1730_; uint8_t v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1729_ = lean_st_ref_get(v_a_1727_);
v_env_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc_ref(v_env_1730_);
lean_dec(v___x_1729_);
v___x_1731_ = 1;
v___x_1732_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_1733_ = l_Lean_Compiler_LCNF_getSigCore_x3f(v___x_1731_, v_env_1730_, v___x_1732_, v_declName_1726_);
v___x_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg___boxed(lean_object* v_declName_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_1735_, v_a_1736_);
lean_dec(v_a_1736_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f(lean_object* v_declName_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_1739_, v_a_1741_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___boxed(lean_object* v_declName_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f(v_declName_1744_, v_a_1745_, v_a_1746_);
lean_dec(v_a_1746_);
lean_dec_ref(v_a_1745_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveBaseDeclCore(lean_object* v_env_1749_, lean_object* v_decl_1750_){
_start:
{
lean_object* v___x_1751_; lean_object* v_toEnvExtension_1752_; lean_object* v_asyncMode_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1751_ = l_Lean_Compiler_LCNF_baseExt;
v_toEnvExtension_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc_ref(v_toEnvExtension_1752_);
v_asyncMode_1753_ = lean_ctor_get(v_toEnvExtension_1752_, 2);
lean_inc(v_asyncMode_1753_);
lean_dec_ref(v_toEnvExtension_1752_);
v___x_1754_ = lean_box(0);
v___x_1755_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1751_, v_env_1749_, v_decl_1750_, v_asyncMode_1753_, v___x_1754_);
lean_dec(v_asyncMode_1753_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveMonoDeclCore(lean_object* v_env_1756_, lean_object* v_decl_1757_){
_start:
{
lean_object* v___x_1758_; lean_object* v_toEnvExtension_1759_; lean_object* v_asyncMode_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1758_ = l_Lean_Compiler_LCNF_monoExt;
v_toEnvExtension_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc_ref(v_toEnvExtension_1759_);
v_asyncMode_1760_ = lean_ctor_get(v_toEnvExtension_1759_, 2);
lean_inc(v_asyncMode_1760_);
lean_dec_ref(v_toEnvExtension_1759_);
v___x_1761_ = lean_box(0);
v___x_1762_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1758_, v_env_1756_, v_decl_1757_, v_asyncMode_1760_, v___x_1761_);
lean_dec(v_asyncMode_1760_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveImpureDeclCore___lam__0(lean_object* v_toSignature_1763_, lean_object* v_decl_1764_, lean_object* v_s_1765_){
_start:
{
lean_object* v_name_1766_; lean_object* v___x_1767_; 
v_name_1766_ = lean_ctor_get(v_toSignature_1763_, 0);
lean_inc(v_name_1766_);
lean_dec_ref(v_toSignature_1763_);
v___x_1767_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_s_1765_, v_name_1766_, v_decl_1764_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveImpureDeclCore(lean_object* v_env_1768_, lean_object* v_decl_1769_){
_start:
{
lean_object* v___x_1770_; lean_object* v_asyncMode_1771_; lean_object* v_toSignature_1772_; lean_object* v___x_1773_; lean_object* v_toEnvExtension_1774_; lean_object* v_asyncMode_1775_; lean_object* v___f_1776_; lean_object* v___x_1777_; lean_object* v_env_1778_; lean_object* v___x_1779_; 
v___x_1770_ = l_Lean_Compiler_LCNF_impureExt;
v_asyncMode_1771_ = lean_ctor_get(v___x_1770_, 2);
lean_inc(v_asyncMode_1771_);
v_toSignature_1772_ = lean_ctor_get(v_decl_1769_, 0);
lean_inc_ref(v_toSignature_1772_);
v___x_1773_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc_ref(v_toEnvExtension_1774_);
v_asyncMode_1775_ = lean_ctor_get(v_toEnvExtension_1774_, 2);
lean_inc(v_asyncMode_1775_);
lean_dec_ref(v_toEnvExtension_1774_);
lean_inc_ref(v_toSignature_1772_);
v___f_1776_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_saveImpureDeclCore___lam__0), 3, 2);
lean_closure_set(v___f_1776_, 0, v_toSignature_1772_);
lean_closure_set(v___f_1776_, 1, v_decl_1769_);
v___x_1777_ = lean_box(0);
v_env_1778_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1770_, v_env_1768_, v___f_1776_, v_asyncMode_1771_, v___x_1777_);
lean_dec(v_asyncMode_1771_);
v___x_1779_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1773_, v_env_1778_, v_toSignature_1772_, v_asyncMode_1775_, v___x_1777_);
lean_dec(v_asyncMode_1775_);
return v___x_1779_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0(void){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1780_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1(void){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0, &l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0);
v___x_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
return v___x_1782_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2(void){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1, &l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1);
v___x_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___redArg(lean_object* v_decl_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v___x_1788_; lean_object* v_env_1789_; lean_object* v_nextMacroScope_1790_; lean_object* v_ngen_1791_; lean_object* v_auxDeclNGen_1792_; lean_object* v_traceState_1793_; lean_object* v_messages_1794_; lean_object* v_infoState_1795_; lean_object* v_snapshotTasks_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1808_; 
v___x_1788_ = lean_st_ref_take(v_a_1786_);
v_env_1789_ = lean_ctor_get(v___x_1788_, 0);
v_nextMacroScope_1790_ = lean_ctor_get(v___x_1788_, 1);
v_ngen_1791_ = lean_ctor_get(v___x_1788_, 2);
v_auxDeclNGen_1792_ = lean_ctor_get(v___x_1788_, 3);
v_traceState_1793_ = lean_ctor_get(v___x_1788_, 4);
v_messages_1794_ = lean_ctor_get(v___x_1788_, 6);
v_infoState_1795_ = lean_ctor_get(v___x_1788_, 7);
v_snapshotTasks_1796_ = lean_ctor_get(v___x_1788_, 8);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1808_ == 0)
{
lean_object* v_unused_1809_; 
v_unused_1809_ = lean_ctor_get(v___x_1788_, 5);
lean_dec(v_unused_1809_);
v___x_1798_ = v___x_1788_;
v_isShared_1799_ = v_isSharedCheck_1808_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_snapshotTasks_1796_);
lean_inc(v_infoState_1795_);
lean_inc(v_messages_1794_);
lean_inc(v_traceState_1793_);
lean_inc(v_auxDeclNGen_1792_);
lean_inc(v_ngen_1791_);
lean_inc(v_nextMacroScope_1790_);
lean_inc(v_env_1789_);
lean_dec(v___x_1788_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1808_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1803_; 
v___x_1800_ = l_Lean_Compiler_LCNF_saveBaseDeclCore(v_env_1789_, v_decl_1785_);
v___x_1801_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2, &l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 5, v___x_1801_);
lean_ctor_set(v___x_1798_, 0, v___x_1800_);
v___x_1803_ = v___x_1798_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1800_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_nextMacroScope_1790_);
lean_ctor_set(v_reuseFailAlloc_1807_, 2, v_ngen_1791_);
lean_ctor_set(v_reuseFailAlloc_1807_, 3, v_auxDeclNGen_1792_);
lean_ctor_set(v_reuseFailAlloc_1807_, 4, v_traceState_1793_);
lean_ctor_set(v_reuseFailAlloc_1807_, 5, v___x_1801_);
lean_ctor_set(v_reuseFailAlloc_1807_, 6, v_messages_1794_);
lean_ctor_set(v_reuseFailAlloc_1807_, 7, v_infoState_1795_);
lean_ctor_set(v_reuseFailAlloc_1807_, 8, v_snapshotTasks_1796_);
v___x_1803_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = lean_st_ref_set(v_a_1786_, v___x_1803_);
v___x_1805_ = lean_box(0);
v___x_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
return v___x_1806_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___redArg___boxed(lean_object* v_decl_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(v_decl_1810_, v_a_1811_);
lean_dec(v_a_1811_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveBase(lean_object* v_decl_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(v_decl_1814_, v_a_1816_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___boxed(lean_object* v_decl_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_Compiler_LCNF_Decl_saveBase(v_decl_1819_, v_a_1820_, v_a_1821_);
lean_dec(v_a_1821_);
lean_dec_ref(v_a_1820_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg(lean_object* v_decl_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v___x_1827_; lean_object* v_env_1828_; lean_object* v_nextMacroScope_1829_; lean_object* v_ngen_1830_; lean_object* v_auxDeclNGen_1831_; lean_object* v_traceState_1832_; lean_object* v_messages_1833_; lean_object* v_infoState_1834_; lean_object* v_snapshotTasks_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1847_; 
v___x_1827_ = lean_st_ref_take(v_a_1825_);
v_env_1828_ = lean_ctor_get(v___x_1827_, 0);
v_nextMacroScope_1829_ = lean_ctor_get(v___x_1827_, 1);
v_ngen_1830_ = lean_ctor_get(v___x_1827_, 2);
v_auxDeclNGen_1831_ = lean_ctor_get(v___x_1827_, 3);
v_traceState_1832_ = lean_ctor_get(v___x_1827_, 4);
v_messages_1833_ = lean_ctor_get(v___x_1827_, 6);
v_infoState_1834_ = lean_ctor_get(v___x_1827_, 7);
v_snapshotTasks_1835_ = lean_ctor_get(v___x_1827_, 8);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1847_ == 0)
{
lean_object* v_unused_1848_; 
v_unused_1848_ = lean_ctor_get(v___x_1827_, 5);
lean_dec(v_unused_1848_);
v___x_1837_ = v___x_1827_;
v_isShared_1838_ = v_isSharedCheck_1847_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_snapshotTasks_1835_);
lean_inc(v_infoState_1834_);
lean_inc(v_messages_1833_);
lean_inc(v_traceState_1832_);
lean_inc(v_auxDeclNGen_1831_);
lean_inc(v_ngen_1830_);
lean_inc(v_nextMacroScope_1829_);
lean_inc(v_env_1828_);
lean_dec(v___x_1827_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1847_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1842_; 
v___x_1839_ = l_Lean_Compiler_LCNF_saveMonoDeclCore(v_env_1828_, v_decl_1824_);
v___x_1840_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2, &l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 5, v___x_1840_);
lean_ctor_set(v___x_1837_, 0, v___x_1839_);
v___x_1842_ = v___x_1837_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1839_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v_nextMacroScope_1829_);
lean_ctor_set(v_reuseFailAlloc_1846_, 2, v_ngen_1830_);
lean_ctor_set(v_reuseFailAlloc_1846_, 3, v_auxDeclNGen_1831_);
lean_ctor_set(v_reuseFailAlloc_1846_, 4, v_traceState_1832_);
lean_ctor_set(v_reuseFailAlloc_1846_, 5, v___x_1840_);
lean_ctor_set(v_reuseFailAlloc_1846_, 6, v_messages_1833_);
lean_ctor_set(v_reuseFailAlloc_1846_, 7, v_infoState_1834_);
lean_ctor_set(v_reuseFailAlloc_1846_, 8, v_snapshotTasks_1835_);
v___x_1842_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1843_ = lean_st_ref_set(v_a_1825_, v___x_1842_);
v___x_1844_ = lean_box(0);
v___x_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
return v___x_1845_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg___boxed(lean_object* v_decl_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v_decl_1849_, v_a_1850_);
lean_dec(v_a_1850_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveMono(lean_object* v_decl_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v_decl_1853_, v_a_1855_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___boxed(lean_object* v_decl_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_Compiler_LCNF_Decl_saveMono(v_decl_1858_, v_a_1859_, v_a_1860_);
lean_dec(v_a_1860_);
lean_dec_ref(v_a_1859_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(lean_object* v_decl_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v___x_1866_; lean_object* v_env_1867_; lean_object* v_nextMacroScope_1868_; lean_object* v_ngen_1869_; lean_object* v_auxDeclNGen_1870_; lean_object* v_traceState_1871_; lean_object* v_messages_1872_; lean_object* v_infoState_1873_; lean_object* v_snapshotTasks_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1886_; 
v___x_1866_ = lean_st_ref_take(v_a_1864_);
v_env_1867_ = lean_ctor_get(v___x_1866_, 0);
v_nextMacroScope_1868_ = lean_ctor_get(v___x_1866_, 1);
v_ngen_1869_ = lean_ctor_get(v___x_1866_, 2);
v_auxDeclNGen_1870_ = lean_ctor_get(v___x_1866_, 3);
v_traceState_1871_ = lean_ctor_get(v___x_1866_, 4);
v_messages_1872_ = lean_ctor_get(v___x_1866_, 6);
v_infoState_1873_ = lean_ctor_get(v___x_1866_, 7);
v_snapshotTasks_1874_ = lean_ctor_get(v___x_1866_, 8);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1886_ == 0)
{
lean_object* v_unused_1887_; 
v_unused_1887_ = lean_ctor_get(v___x_1866_, 5);
lean_dec(v_unused_1887_);
v___x_1876_ = v___x_1866_;
v_isShared_1877_ = v_isSharedCheck_1886_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_snapshotTasks_1874_);
lean_inc(v_infoState_1873_);
lean_inc(v_messages_1872_);
lean_inc(v_traceState_1871_);
lean_inc(v_auxDeclNGen_1870_);
lean_inc(v_ngen_1869_);
lean_inc(v_nextMacroScope_1868_);
lean_inc(v_env_1867_);
lean_dec(v___x_1866_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1886_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1881_; 
v___x_1878_ = l_Lean_Compiler_LCNF_saveImpureDeclCore(v_env_1867_, v_decl_1863_);
v___x_1879_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2, &l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 5, v___x_1879_);
lean_ctor_set(v___x_1876_, 0, v___x_1878_);
v___x_1881_ = v___x_1876_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v_nextMacroScope_1868_);
lean_ctor_set(v_reuseFailAlloc_1885_, 2, v_ngen_1869_);
lean_ctor_set(v_reuseFailAlloc_1885_, 3, v_auxDeclNGen_1870_);
lean_ctor_set(v_reuseFailAlloc_1885_, 4, v_traceState_1871_);
lean_ctor_set(v_reuseFailAlloc_1885_, 5, v___x_1879_);
lean_ctor_set(v_reuseFailAlloc_1885_, 6, v_messages_1872_);
lean_ctor_set(v_reuseFailAlloc_1885_, 7, v_infoState_1873_);
lean_ctor_set(v_reuseFailAlloc_1885_, 8, v_snapshotTasks_1874_);
v___x_1881_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1882_ = lean_st_ref_set(v_a_1864_, v___x_1881_);
v___x_1883_ = lean_box(0);
v___x_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
return v___x_1884_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___redArg___boxed(lean_object* v_decl_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_decl_1888_, v_a_1889_);
lean_dec(v_a_1889_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure(lean_object* v_decl_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v___x_1896_; 
v___x_1896_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_decl_1892_, v_a_1894_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___boxed(lean_object* v_decl_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_Compiler_LCNF_Decl_saveImpure(v_decl_1897_, v_a_1898_, v_a_1899_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__0(lean_object* v_decl_1902_, lean_object* v_h_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(v_decl_1902_, v___y_1907_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__0___boxed(lean_object* v_decl_1910_, lean_object* v_h_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_Compiler_LCNF_Decl_save___lam__0(v_decl_1910_, v_h_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__1(lean_object* v_decl_1918_, lean_object* v_h_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v_decl_1918_, v___y_1923_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__1___boxed(lean_object* v_decl_1926_, lean_object* v_h_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Lean_Compiler_LCNF_Decl_save___lam__1(v_decl_1926_, v_h_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__2(lean_object* v_decl_1934_, lean_object* v_h_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_decl_1934_, v___y_1939_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__2___boxed(lean_object* v_decl_1942_, lean_object* v_h_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_Compiler_LCNF_Decl_save___lam__2(v_decl_1942_, v_h_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
return v_res_1949_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_save___closed__0(void){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_1950_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_save___closed__1(void){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_save___closed__0, &l_Lean_Compiler_LCNF_Decl_save___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_save___closed__0);
v___x_1952_ = l_ReaderT_instMonad___redArg(v___x_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save(uint8_t v_pu_1955_, lean_object* v_decl_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v___x_1962_; lean_object* v_toApplicative_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_2017_; 
v___x_1962_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_save___closed__1, &l_Lean_Compiler_LCNF_Decl_save___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_save___closed__1);
v_toApplicative_1963_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_2017_ == 0)
{
lean_object* v_unused_2018_; 
v_unused_2018_ = lean_ctor_get(v___x_1962_, 1);
lean_dec(v_unused_2018_);
v___x_1965_ = v___x_1962_;
v_isShared_1966_ = v_isSharedCheck_2017_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_toApplicative_1963_);
lean_dec(v___x_1962_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_2017_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v_toFunctor_1967_; lean_object* v_toSeq_1968_; lean_object* v_toSeqLeft_1969_; lean_object* v_toSeqRight_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2015_; 
v_toFunctor_1967_ = lean_ctor_get(v_toApplicative_1963_, 0);
v_toSeq_1968_ = lean_ctor_get(v_toApplicative_1963_, 2);
v_toSeqLeft_1969_ = lean_ctor_get(v_toApplicative_1963_, 3);
v_toSeqRight_1970_ = lean_ctor_get(v_toApplicative_1963_, 4);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_toApplicative_1963_);
if (v_isSharedCheck_2015_ == 0)
{
lean_object* v_unused_2016_; 
v_unused_2016_ = lean_ctor_get(v_toApplicative_1963_, 1);
lean_dec(v_unused_2016_);
v___x_1972_ = v_toApplicative_1963_;
v_isShared_1973_ = v_isSharedCheck_2015_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_toSeqRight_1970_);
lean_inc(v_toSeqLeft_1969_);
lean_inc(v_toSeq_1968_);
lean_inc(v_toFunctor_1967_);
lean_dec(v_toApplicative_1963_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2015_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___f_1974_; lean_object* v___f_1975_; lean_object* v___f_1976_; lean_object* v___f_1977_; lean_object* v___x_1978_; lean_object* v___f_1979_; lean_object* v___f_1980_; lean_object* v___f_1981_; lean_object* v___x_1983_; 
v___f_1974_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_save___closed__2));
v___f_1975_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_save___closed__3));
lean_inc_ref(v_toFunctor_1967_);
v___f_1976_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1976_, 0, v_toFunctor_1967_);
v___f_1977_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1977_, 0, v_toFunctor_1967_);
v___x_1978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___f_1976_);
lean_ctor_set(v___x_1978_, 1, v___f_1977_);
v___f_1979_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1979_, 0, v_toSeqRight_1970_);
v___f_1980_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1980_, 0, v_toSeqLeft_1969_);
v___f_1981_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1981_, 0, v_toSeq_1968_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 4, v___f_1979_);
lean_ctor_set(v___x_1972_, 3, v___f_1980_);
lean_ctor_set(v___x_1972_, 2, v___f_1981_);
lean_ctor_set(v___x_1972_, 1, v___f_1974_);
lean_ctor_set(v___x_1972_, 0, v___x_1978_);
v___x_1983_ = v___x_1972_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_1978_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v___f_1974_);
lean_ctor_set(v_reuseFailAlloc_2014_, 2, v___f_1981_);
lean_ctor_set(v_reuseFailAlloc_2014_, 3, v___f_1980_);
lean_ctor_set(v_reuseFailAlloc_2014_, 4, v___f_1979_);
v___x_1983_ = v_reuseFailAlloc_2014_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
lean_object* v___x_1985_; 
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 1, v___f_1975_);
lean_ctor_set(v___x_1965_, 0, v___x_1983_);
v___x_1985_ = v___x_1965_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_1983_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v___f_1975_);
v___x_1985_ = v_reuseFailAlloc_2013_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = l_ReaderT_instMonad___redArg(v___x_1985_);
v___x_1987_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_1957_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___f_1991_; uint8_t v___x_1992_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_1988_);
lean_dec_ref(v___x_1987_);
v___x_1989_ = lean_box(0);
v___x_1990_ = l_instInhabitedOfMonad___redArg(v___x_1986_, v___x_1989_);
v___f_1991_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1991_, 0, v___x_1990_);
v___x_1992_ = lean_unbox(v_a_1988_);
switch(v___x_1992_)
{
case 0:
{
lean_object* v___f_1993_; uint8_t v___x_1994_; lean_object* v___x_384__overap_1995_; lean_object* v___x_1996_; 
v___f_1993_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_save___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1993_, 0, v_decl_1956_);
v___x_1994_ = lean_unbox(v_a_1988_);
lean_dec(v_a_1988_);
v___x_384__overap_1995_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___f_1991_, v___x_1994_, v_pu_1955_, v___f_1993_);
v___x_1996_ = lean_apply_5(v___x_384__overap_1995_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, lean_box(0));
return v___x_1996_;
}
case 1:
{
lean_object* v___f_1997_; uint8_t v___x_1998_; lean_object* v___x_402__overap_1999_; lean_object* v___x_2000_; 
v___f_1997_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_save___lam__1___boxed), 7, 1);
lean_closure_set(v___f_1997_, 0, v_decl_1956_);
v___x_1998_ = lean_unbox(v_a_1988_);
lean_dec(v_a_1988_);
v___x_402__overap_1999_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___f_1991_, v___x_1998_, v_pu_1955_, v___f_1997_);
v___x_2000_ = lean_apply_5(v___x_402__overap_1999_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, lean_box(0));
return v___x_2000_;
}
default: 
{
lean_object* v___f_2001_; uint8_t v___x_2002_; lean_object* v___x_420__overap_2003_; lean_object* v___x_2004_; 
v___f_2001_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_save___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2001_, 0, v_decl_1956_);
v___x_2002_ = lean_unbox(v_a_1988_);
lean_dec(v_a_1988_);
v___x_420__overap_2003_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___f_1991_, v___x_2002_, v_pu_1955_, v___f_2001_);
v___x_2004_ = lean_apply_5(v___x_420__overap_2003_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, lean_box(0));
return v___x_2004_;
}
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec_ref(v___x_1986_);
lean_dec(v_a_1960_);
lean_dec_ref(v_a_1959_);
lean_dec(v_a_1958_);
lean_dec_ref(v_a_1957_);
lean_dec_ref(v_decl_1956_);
v_a_2005_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1987_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_1987_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___boxed(lean_object* v_pu_2019_, lean_object* v_decl_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
uint8_t v_pu_boxed_2026_; lean_object* v_res_2027_; 
v_pu_boxed_2026_ = lean_unbox(v_pu_2019_);
v_res_2027_ = l_Lean_Compiler_LCNF_Decl_save(v_pu_boxed_2026_, v_decl_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
return v_res_2027_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2028_; 
v___x_2028_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2028_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0);
v___x_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
return v___x_2030_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2031_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1);
v___x_2032_ = lean_unsigned_to_nat(0u);
v___x_2033_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
lean_ctor_set(v___x_2033_, 2, v___x_2032_);
lean_ctor_set(v___x_2033_, 3, v___x_2031_);
lean_ctor_set(v___x_2033_, 4, v___x_2031_);
lean_ctor_set(v___x_2033_, 5, v___x_2031_);
lean_ctor_set(v___x_2033_, 6, v___x_2031_);
lean_ctor_set(v___x_2033_, 7, v___x_2031_);
lean_ctor_set(v___x_2033_, 8, v___x_2031_);
return v___x_2033_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2034_ = lean_unsigned_to_nat(32u);
v___x_2035_ = lean_mk_empty_array_with_capacity(v___x_2034_);
v___x_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
return v___x_2036_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2037_ = ((size_t)5ULL);
v___x_2038_ = lean_unsigned_to_nat(0u);
v___x_2039_ = lean_unsigned_to_nat(32u);
v___x_2040_ = lean_mk_empty_array_with_capacity(v___x_2039_);
v___x_2041_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3);
v___x_2042_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
lean_ctor_set(v___x_2042_, 1, v___x_2040_);
lean_ctor_set(v___x_2042_, 2, v___x_2038_);
lean_ctor_set(v___x_2042_, 3, v___x_2038_);
lean_ctor_set_usize(v___x_2042_, 4, v___x_2037_);
return v___x_2042_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2043_ = lean_box(1);
v___x_2044_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4);
v___x_2045_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1);
v___x_2046_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
lean_ctor_set(v___x_2046_, 1, v___x_2044_);
lean_ctor_set(v___x_2046_, 2, v___x_2043_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0(lean_object* v_msgData_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v___x_2051_; lean_object* v_env_2052_; lean_object* v_options_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2051_ = lean_st_ref_get(v___y_2049_);
v_env_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc_ref(v_env_2052_);
lean_dec(v___x_2051_);
v_options_2053_ = lean_ctor_get(v___y_2048_, 2);
v___x_2054_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2);
v___x_2055_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_2053_);
v___x_2056_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2056_, 0, v_env_2052_);
lean_ctor_set(v___x_2056_, 1, v___x_2054_);
lean_ctor_set(v___x_2056_, 2, v___x_2055_);
lean_ctor_set(v___x_2056_, 3, v_options_2053_);
v___x_2057_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2056_);
lean_ctor_set(v___x_2057_, 1, v_msgData_2047_);
v___x_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___boxed(lean_object* v_msgData_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0(v_msgData_2059_, v___y_2060_, v___y_2061_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg(lean_object* v_msg_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_ref_2068_; lean_object* v___x_2069_; lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2078_; 
v_ref_2068_ = lean_ctor_get(v___y_2065_, 5);
v___x_2069_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0(v_msg_2064_, v___y_2065_, v___y_2066_);
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2072_ = v___x_2069_;
v_isShared_2073_ = v_isSharedCheck_2078_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2069_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2078_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2074_; lean_object* v___x_2076_; 
lean_inc(v_ref_2068_);
v___x_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2074_, 0, v_ref_2068_);
lean_ctor_set(v___x_2074_, 1, v_a_2070_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set_tag(v___x_2072_, 1);
lean_ctor_set(v___x_2072_, 0, v___x_2074_);
v___x_2076_ = v___x_2072_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2074_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg___boxed(lean_object* v_msg_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg(v_msg_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
return v_res_2083_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = ((lean_object*)(l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__0));
v___x_2086_ = l_Lean_stringToMessageData(v___x_2085_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f(lean_object* v_declName_2087_, uint8_t v_phase_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_){
_start:
{
switch(v_phase_2088_)
{
case 0:
{
lean_object* v___x_2092_; 
v___x_2092_ = l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg(v_declName_2087_, v_a_2090_);
return v___x_2092_;
}
case 1:
{
lean_object* v___x_2093_; 
v___x_2093_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_2087_, v_a_2090_);
return v___x_2093_;
}
default: 
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
lean_dec(v_declName_2087_);
v___x_2094_ = lean_obj_once(&l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1, &l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1_once, _init_l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1);
v___x_2095_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg(v___x_2094_, v_a_2089_, v_a_2090_);
return v___x_2095_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f___boxed(lean_object* v_declName_2096_, lean_object* v_phase_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
uint8_t v_phase_boxed_2101_; lean_object* v_res_2102_; 
v_phase_boxed_2101_ = lean_unbox(v_phase_2097_);
v_res_2102_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_2096_, v_phase_boxed_2101_, v_a_2098_, v_a_2099_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0(lean_object* v_00_u03b1_2103_, lean_object* v_msg_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v___x_2108_; 
v___x_2108_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg(v_msg_2104_, v___y_2105_, v___y_2106_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___boxed(lean_object* v_00_u03b1_2109_, lean_object* v_msg_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0(v_00_u03b1_2109_, v_msg_2110_, v___y_2111_, v___y_2112_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg(lean_object* v_declName_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_2116_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; uint8_t v___x_2122_; lean_object* v___x_2123_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref(v___x_2120_);
v___x_2122_ = lean_unbox(v_a_2121_);
v___x_2123_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_2115_, v___x_2122_, v_a_2117_, v_a_2118_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2147_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2126_ = v___x_2123_;
v_isShared_2127_ = v_isSharedCheck_2147_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2123_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2147_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
if (lean_obj_tag(v_a_2124_) == 1)
{
lean_object* v_val_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2142_; 
v_val_2128_ = lean_ctor_get(v_a_2124_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_a_2124_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2130_ = v_a_2124_;
v_isShared_2131_ = v_isSharedCheck_2142_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_val_2128_);
lean_dec(v_a_2124_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2142_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
uint8_t v___x_2132_; uint8_t v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2137_; 
v___x_2132_ = lean_unbox(v_a_2121_);
lean_dec(v_a_2121_);
v___x_2133_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_2132_);
v___x_2134_ = lean_box(v___x_2133_);
v___x_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2134_);
lean_ctor_set(v___x_2135_, 1, v_val_2128_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 0, v___x_2135_);
v___x_2137_ = v___x_2130_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2135_);
v___x_2137_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
lean_object* v___x_2139_; 
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v___x_2137_);
v___x_2139_ = v___x_2126_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
else
{
lean_object* v___x_2143_; lean_object* v___x_2145_; 
lean_dec(v_a_2124_);
lean_dec(v_a_2121_);
v___x_2143_ = lean_box(0);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v___x_2143_);
v___x_2145_ = v___x_2126_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2143_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec(v_a_2121_);
v_a_2148_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2123_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2123_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec(v_declName_2115_);
v_a_2156_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2120_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2120_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg___boxed(lean_object* v_declName_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(v_declName_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
lean_dec(v_a_2167_);
lean_dec_ref(v_a_2166_);
lean_dec_ref(v_a_2165_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDecl_x3f(lean_object* v_declName_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_2171_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; uint8_t v___x_2178_; lean_object* v___x_2179_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref(v___x_2176_);
v___x_2178_ = lean_unbox(v_a_2177_);
v___x_2179_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_2170_, v___x_2178_, v_a_2173_, v_a_2174_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2203_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2182_ = v___x_2179_;
v_isShared_2183_ = v_isSharedCheck_2203_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2179_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2203_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
if (lean_obj_tag(v_a_2180_) == 1)
{
lean_object* v_val_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2198_; 
v_val_2184_ = lean_ctor_get(v_a_2180_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v_a_2180_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2186_ = v_a_2180_;
v_isShared_2187_ = v_isSharedCheck_2198_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_val_2184_);
lean_dec(v_a_2180_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2198_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
uint8_t v___x_2188_; uint8_t v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2193_; 
v___x_2188_ = lean_unbox(v_a_2177_);
lean_dec(v_a_2177_);
v___x_2189_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_2188_);
v___x_2190_ = lean_box(v___x_2189_);
v___x_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
lean_ctor_set(v___x_2191_, 1, v_val_2184_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v___x_2191_);
v___x_2193_ = v___x_2186_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2191_);
v___x_2193_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
lean_object* v___x_2195_; 
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 0, v___x_2193_);
v___x_2195_ = v___x_2182_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2193_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
else
{
lean_object* v___x_2199_; lean_object* v___x_2201_; 
lean_dec(v_a_2180_);
lean_dec(v_a_2177_);
v___x_2199_ = lean_box(0);
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 0, v___x_2199_);
v___x_2201_ = v___x_2182_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2199_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_dec(v_a_2177_);
v_a_2204_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2179_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2179_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_dec(v_declName_2170_);
v_a_2212_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2176_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2176_);
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
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___boxed(lean_object* v_declName_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Lean_Compiler_LCNF_getDecl_x3f(v_declName_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(lean_object* v_declName_2227_, uint8_t v_phase_2228_, lean_object* v_a_2229_){
_start:
{
lean_object* v___x_2231_; 
v___x_2231_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__2, &l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__2);
switch(v_phase_2228_)
{
case 0:
{
lean_object* v___x_2232_; lean_object* v_env_2233_; lean_object* v___x_2234_; lean_object* v_toEnvExtension_2235_; lean_object* v_asyncMode_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2232_ = lean_st_ref_get(v_a_2229_);
v_env_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc_ref(v_env_2233_);
lean_dec(v___x_2232_);
v___x_2234_ = l_Lean_Compiler_LCNF_baseExt;
v_toEnvExtension_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc_ref(v_toEnvExtension_2235_);
v_asyncMode_2236_ = lean_ctor_get(v_toEnvExtension_2235_, 2);
lean_inc(v_asyncMode_2236_);
lean_dec_ref(v_toEnvExtension_2235_);
v___x_2237_ = lean_box(0);
v___x_2238_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2231_, v___x_2234_, v_env_2233_, v_asyncMode_2236_, v___x_2237_);
lean_dec(v_asyncMode_2236_);
v___x_2239_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_2238_, v_declName_2227_);
v___x_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
return v___x_2240_;
}
case 1:
{
lean_object* v___x_2241_; lean_object* v_env_2242_; lean_object* v___x_2243_; lean_object* v_toEnvExtension_2244_; lean_object* v_asyncMode_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2241_ = lean_st_ref_get(v_a_2229_);
v_env_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc_ref(v_env_2242_);
lean_dec(v___x_2241_);
v___x_2243_ = l_Lean_Compiler_LCNF_monoExt;
v_toEnvExtension_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc_ref(v_toEnvExtension_2244_);
v_asyncMode_2245_ = lean_ctor_get(v_toEnvExtension_2244_, 2);
lean_inc(v_asyncMode_2245_);
lean_dec_ref(v_toEnvExtension_2244_);
v___x_2246_ = lean_box(0);
v___x_2247_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2231_, v___x_2243_, v_env_2242_, v_asyncMode_2245_, v___x_2246_);
lean_dec(v_asyncMode_2245_);
v___x_2248_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_2247_, v_declName_2227_);
v___x_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
return v___x_2249_;
}
default: 
{
lean_object* v___x_2250_; lean_object* v_env_2251_; lean_object* v___x_2252_; lean_object* v_asyncMode_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2250_ = lean_st_ref_get(v_a_2229_);
v_env_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc_ref(v_env_2251_);
lean_dec(v___x_2250_);
v___x_2252_ = l_Lean_Compiler_LCNF_impureExt;
v_asyncMode_2253_ = lean_ctor_get(v___x_2252_, 2);
lean_inc(v_asyncMode_2253_);
v___x_2254_ = lean_box(0);
v___x_2255_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2231_, v___x_2252_, v_env_2251_, v_asyncMode_2253_, v___x_2254_);
lean_dec(v_asyncMode_2253_);
v___x_2256_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_2255_, v_declName_2227_);
v___x_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
return v___x_2257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg___boxed(lean_object* v_declName_2258_, lean_object* v_phase_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_){
_start:
{
uint8_t v_phase_boxed_2262_; lean_object* v_res_2263_; 
v_phase_boxed_2262_ = lean_unbox(v_phase_2259_);
v_res_2263_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_declName_2258_, v_phase_boxed_2262_, v_a_2260_);
lean_dec(v_a_2260_);
lean_dec(v_declName_2258_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f(lean_object* v_declName_2264_, uint8_t v_phase_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_declName_2264_, v_phase_2265_, v_a_2269_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___boxed(lean_object* v_declName_2272_, lean_object* v_phase_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_){
_start:
{
uint8_t v_phase_boxed_2279_; lean_object* v_res_2280_; 
v_phase_boxed_2279_ = lean_unbox(v_phase_2273_);
v_res_2280_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f(v_declName_2272_, v_phase_boxed_2279_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_);
lean_dec(v_a_2277_);
lean_dec_ref(v_a_2276_);
lean_dec(v_a_2275_);
lean_dec_ref(v_a_2274_);
lean_dec(v_declName_2272_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDecl_x3f___redArg(lean_object* v_declName_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_2282_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; uint8_t v___x_2287_; lean_object* v___x_2288_; lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2312_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref(v___x_2285_);
v___x_2287_ = lean_unbox(v_a_2286_);
v___x_2288_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_declName_2281_, v___x_2287_, v_a_2283_);
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2291_ = v___x_2288_;
v_isShared_2292_ = v_isSharedCheck_2312_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2288_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2312_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
if (lean_obj_tag(v_a_2289_) == 1)
{
lean_object* v_val_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2307_; 
v_val_2293_ = lean_ctor_get(v_a_2289_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v_a_2289_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2295_ = v_a_2289_;
v_isShared_2296_ = v_isSharedCheck_2307_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_val_2293_);
lean_dec(v_a_2289_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2307_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
uint8_t v___x_2297_; uint8_t v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2302_; 
v___x_2297_ = lean_unbox(v_a_2286_);
lean_dec(v_a_2286_);
v___x_2298_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_2297_);
v___x_2299_ = lean_box(v___x_2298_);
v___x_2300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
lean_ctor_set(v___x_2300_, 1, v_val_2293_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v___x_2300_);
v___x_2302_ = v___x_2295_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2304_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v___x_2302_);
v___x_2304_ = v___x_2291_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2302_);
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
lean_object* v___x_2308_; lean_object* v___x_2310_; 
lean_dec(v_a_2289_);
lean_dec(v_a_2286_);
v___x_2308_ = lean_box(0);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v___x_2308_);
v___x_2310_ = v___x_2291_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2308_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
v_a_2313_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2285_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2285_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDecl_x3f___redArg___boxed(lean_object* v_declName_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_Lean_Compiler_LCNF_getLocalDecl_x3f___redArg(v_declName_2321_, v_a_2322_, v_a_2323_);
lean_dec(v_a_2323_);
lean_dec_ref(v_a_2322_);
lean_dec(v_declName_2321_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDecl_x3f(lean_object* v_declName_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_2327_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; uint8_t v___x_2334_; lean_object* v___x_2335_; lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2359_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref(v___x_2332_);
v___x_2334_ = lean_unbox(v_a_2333_);
v___x_2335_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_declName_2326_, v___x_2334_, v_a_2330_);
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2338_ = v___x_2335_;
v_isShared_2339_ = v_isSharedCheck_2359_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2335_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2359_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
if (lean_obj_tag(v_a_2336_) == 1)
{
lean_object* v_val_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2354_; 
v_val_2340_ = lean_ctor_get(v_a_2336_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v_a_2336_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2342_ = v_a_2336_;
v_isShared_2343_ = v_isSharedCheck_2354_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_val_2340_);
lean_dec(v_a_2336_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2354_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
uint8_t v___x_2344_; uint8_t v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2349_; 
v___x_2344_ = lean_unbox(v_a_2333_);
lean_dec(v_a_2333_);
v___x_2345_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_2344_);
v___x_2346_ = lean_box(v___x_2345_);
v___x_2347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
lean_ctor_set(v___x_2347_, 1, v_val_2340_);
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v___x_2347_);
v___x_2349_ = v___x_2342_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
lean_object* v___x_2351_; 
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 0, v___x_2349_);
v___x_2351_ = v___x_2338_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
else
{
lean_object* v___x_2355_; lean_object* v___x_2357_; 
lean_dec(v_a_2336_);
lean_dec(v_a_2333_);
v___x_2355_ = lean_box(0);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 0, v___x_2355_);
v___x_2357_ = v___x_2338_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2355_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
v_a_2360_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2332_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2332_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDecl_x3f___boxed(lean_object* v_declName_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_Lean_Compiler_LCNF_getLocalDecl_x3f(v_declName_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
lean_dec(v_a_2372_);
lean_dec_ref(v_a_2371_);
lean_dec(v_a_2370_);
lean_dec_ref(v_a_2369_);
lean_dec(v_declName_2368_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2376_; 
v___x_2376_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2____boxed(lean_object* v_a_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2_();
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_recordFinalImpureDecl___lam__0(lean_object* v_name_2379_, lean_object* v_s_2380_){
_start:
{
lean_object* v_fst_2381_; lean_object* v_snd_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2391_; 
v_fst_2381_ = lean_ctor_get(v_s_2380_, 0);
v_snd_2382_ = lean_ctor_get(v_s_2380_, 1);
v_isSharedCheck_2391_ = !lean_is_exclusive(v_s_2380_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2384_ = v_s_2380_;
v_isShared_2385_ = v_isSharedCheck_2391_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_snd_2382_);
lean_inc(v_fst_2381_);
lean_dec(v_s_2380_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2391_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2389_; 
lean_inc(v_name_2379_);
v___x_2386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2386_, 0, v_name_2379_);
lean_ctor_set(v___x_2386_, 1, v_fst_2381_);
v___x_2387_ = l_Lean_NameSet_insert(v_snd_2382_, v_name_2379_);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 1, v___x_2387_);
lean_ctor_set(v___x_2384_, 0, v___x_2386_);
v___x_2389_ = v___x_2384_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2390_, 1, v___x_2387_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_recordFinalImpureDecl(lean_object* v_env_2392_, lean_object* v_name_2393_){
_start:
{
lean_object* v___x_2394_; lean_object* v_asyncMode_2395_; lean_object* v___f_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2394_ = l_Lean_Compiler_LCNF_declOrderExt;
v_asyncMode_2395_ = lean_ctor_get(v___x_2394_, 2);
lean_inc(v_asyncMode_2395_);
v___f_2396_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_recordFinalImpureDecl___lam__0), 2, 1);
lean_closure_set(v___f_2396_, 0, v_name_2393_);
v___x_2397_ = lean_box(0);
v___x_2398_ = l_Lean_EnvExtension_modifyState___redArg(v___x_2394_, v_env_2392_, v___f_2396_, v_asyncMode_2395_, v___x_2397_);
lean_dec(v_asyncMode_2395_);
return v___x_2398_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7(void){
_start:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2406_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__1));
v___x_2407_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___closed__0));
v___x_2408_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2407_, v___x_2406_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1(lean_object* v_msg_2409_){
_start:
{
lean_object* v___f_2410_; lean_object* v___f_2411_; lean_object* v___f_2412_; lean_object* v___f_2413_; lean_object* v___f_2414_; lean_object* v___f_2415_; lean_object* v___f_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___f_2410_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__0));
v___f_2411_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__1));
v___f_2412_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__2));
v___f_2413_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__3));
v___f_2414_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__4));
v___f_2415_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__5));
v___f_2416_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__6));
v___x_2417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2417_, 0, v___f_2410_);
lean_ctor_set(v___x_2417_, 1, v___f_2411_);
v___x_2418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
lean_ctor_set(v___x_2418_, 1, v___f_2412_);
lean_ctor_set(v___x_2418_, 2, v___f_2413_);
lean_ctor_set(v___x_2418_, 3, v___f_2414_);
lean_ctor_set(v___x_2418_, 4, v___f_2415_);
v___x_2419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
lean_ctor_set(v___x_2419_, 1, v___f_2416_);
v___x_2420_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7, &l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7_once, _init_l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7);
v___x_2421_ = lean_unsigned_to_nat(0u);
v___x_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2420_);
lean_ctor_set(v___x_2422_, 1, v___x_2421_);
v___x_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
v___x_2424_ = l_instInhabitedOfMonad___redArg(v___x_2419_, v___x_2423_);
v___x_2425_ = lean_panic_fn(v___x_2424_, v_msg_2409_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__5(lean_object* v_msg_2426_){
_start:
{
lean_object* v___f_2427_; lean_object* v___f_2428_; lean_object* v___f_2429_; lean_object* v___f_2430_; lean_object* v___f_2431_; lean_object* v___f_2432_; lean_object* v___f_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___f_2427_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__0));
v___f_2428_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__1));
v___f_2429_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__2));
v___f_2430_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__3));
v___f_2431_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__4));
v___f_2432_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__5));
v___f_2433_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__6));
v___x_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___f_2427_);
lean_ctor_set(v___x_2434_, 1, v___f_2428_);
v___x_2435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2434_);
lean_ctor_set(v___x_2435_, 1, v___f_2429_);
lean_ctor_set(v___x_2435_, 2, v___f_2430_);
lean_ctor_set(v___x_2435_, 3, v___f_2431_);
lean_ctor_set(v___x_2435_, 4, v___f_2432_);
v___x_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
lean_ctor_set(v___x_2436_, 1, v___f_2433_);
v___x_2437_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7, &l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7_once, _init_l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7);
v___x_2438_ = l_instInhabitedOfMonad___redArg(v___x_2436_, v___x_2437_);
v___x_2439_ = lean_panic_fn(v___x_2438_, v_msg_2426_);
return v___x_2439_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(lean_object* v_a_2440_, lean_object* v_x_2441_){
_start:
{
if (lean_obj_tag(v_x_2441_) == 0)
{
uint8_t v___x_2442_; 
v___x_2442_ = 0;
return v___x_2442_;
}
else
{
lean_object* v_key_2443_; lean_object* v_tail_2444_; uint8_t v___x_2445_; 
v_key_2443_ = lean_ctor_get(v_x_2441_, 0);
v_tail_2444_ = lean_ctor_get(v_x_2441_, 2);
v___x_2445_ = lean_name_eq(v_key_2443_, v_a_2440_);
if (v___x_2445_ == 0)
{
v_x_2441_ = v_tail_2444_;
goto _start;
}
else
{
return v___x_2445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg___boxed(lean_object* v_a_2447_, lean_object* v_x_2448_){
_start:
{
uint8_t v_res_2449_; lean_object* v_r_2450_; 
v_res_2449_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_2447_, v_x_2448_);
lean_dec(v_x_2448_);
lean_dec(v_a_2447_);
v_r_2450_ = lean_box(v_res_2449_);
return v_r_2450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8_spec__10___redArg(lean_object* v_x_2451_, lean_object* v_x_2452_){
_start:
{
if (lean_obj_tag(v_x_2452_) == 0)
{
return v_x_2451_;
}
else
{
lean_object* v_key_2453_; lean_object* v_value_2454_; lean_object* v_tail_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2481_; 
v_key_2453_ = lean_ctor_get(v_x_2452_, 0);
v_value_2454_ = lean_ctor_get(v_x_2452_, 1);
v_tail_2455_ = lean_ctor_get(v_x_2452_, 2);
v_isSharedCheck_2481_ = !lean_is_exclusive(v_x_2452_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2457_ = v_x_2452_;
v_isShared_2458_ = v_isSharedCheck_2481_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_tail_2455_);
lean_inc(v_value_2454_);
lean_inc(v_key_2453_);
lean_dec(v_x_2452_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2481_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2459_; uint64_t v___y_2461_; 
v___x_2459_ = lean_array_get_size(v_x_2451_);
if (lean_obj_tag(v_key_2453_) == 0)
{
uint64_t v___x_2479_; 
v___x_2479_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0);
v___y_2461_ = v___x_2479_;
goto v___jp_2460_;
}
else
{
uint64_t v_hash_2480_; 
v_hash_2480_ = lean_ctor_get_uint64(v_key_2453_, sizeof(void*)*2);
v___y_2461_ = v_hash_2480_;
goto v___jp_2460_;
}
v___jp_2460_:
{
uint64_t v___x_2462_; uint64_t v___x_2463_; uint64_t v_fold_2464_; uint64_t v___x_2465_; uint64_t v___x_2466_; uint64_t v___x_2467_; size_t v___x_2468_; size_t v___x_2469_; size_t v___x_2470_; size_t v___x_2471_; size_t v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2475_; 
v___x_2462_ = 32ULL;
v___x_2463_ = lean_uint64_shift_right(v___y_2461_, v___x_2462_);
v_fold_2464_ = lean_uint64_xor(v___y_2461_, v___x_2463_);
v___x_2465_ = 16ULL;
v___x_2466_ = lean_uint64_shift_right(v_fold_2464_, v___x_2465_);
v___x_2467_ = lean_uint64_xor(v_fold_2464_, v___x_2466_);
v___x_2468_ = lean_uint64_to_usize(v___x_2467_);
v___x_2469_ = lean_usize_of_nat(v___x_2459_);
v___x_2470_ = ((size_t)1ULL);
v___x_2471_ = lean_usize_sub(v___x_2469_, v___x_2470_);
v___x_2472_ = lean_usize_land(v___x_2468_, v___x_2471_);
v___x_2473_ = lean_array_uget_borrowed(v_x_2451_, v___x_2472_);
lean_inc(v___x_2473_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 2, v___x_2473_);
v___x_2475_ = v___x_2457_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_key_2453_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_value_2454_);
lean_ctor_set(v_reuseFailAlloc_2478_, 2, v___x_2473_);
v___x_2475_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2476_; 
v___x_2476_ = lean_array_uset(v_x_2451_, v___x_2472_, v___x_2475_);
v_x_2451_ = v___x_2476_;
v_x_2452_ = v_tail_2455_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8___redArg(lean_object* v_i_2482_, lean_object* v_source_2483_, lean_object* v_target_2484_){
_start:
{
lean_object* v___x_2485_; uint8_t v___x_2486_; 
v___x_2485_ = lean_array_get_size(v_source_2483_);
v___x_2486_ = lean_nat_dec_lt(v_i_2482_, v___x_2485_);
if (v___x_2486_ == 0)
{
lean_dec_ref(v_source_2483_);
lean_dec(v_i_2482_);
return v_target_2484_;
}
else
{
lean_object* v_es_2487_; lean_object* v___x_2488_; lean_object* v_source_2489_; lean_object* v_target_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v_es_2487_ = lean_array_fget(v_source_2483_, v_i_2482_);
v___x_2488_ = lean_box(0);
v_source_2489_ = lean_array_fset(v_source_2483_, v_i_2482_, v___x_2488_);
v_target_2490_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8_spec__10___redArg(v_target_2484_, v_es_2487_);
v___x_2491_ = lean_unsigned_to_nat(1u);
v___x_2492_ = lean_nat_add(v_i_2482_, v___x_2491_);
lean_dec(v_i_2482_);
v_i_2482_ = v___x_2492_;
v_source_2483_ = v_source_2489_;
v_target_2484_ = v_target_2490_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6___redArg(lean_object* v_data_2494_){
_start:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v_nbuckets_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2495_ = lean_array_get_size(v_data_2494_);
v___x_2496_ = lean_unsigned_to_nat(2u);
v_nbuckets_2497_ = lean_nat_mul(v___x_2495_, v___x_2496_);
v___x_2498_ = lean_unsigned_to_nat(0u);
v___x_2499_ = lean_box(0);
v___x_2500_ = lean_mk_array(v_nbuckets_2497_, v___x_2499_);
v___x_2501_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8___redArg(v___x_2498_, v_data_2494_, v___x_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__0___redArg(lean_object* v_m_2502_, lean_object* v_a_2503_, lean_object* v_b_2504_){
_start:
{
lean_object* v_size_2505_; lean_object* v_buckets_2506_; lean_object* v___x_2507_; uint64_t v___y_2509_; 
v_size_2505_ = lean_ctor_get(v_m_2502_, 0);
v_buckets_2506_ = lean_ctor_get(v_m_2502_, 1);
v___x_2507_ = lean_array_get_size(v_buckets_2506_);
if (lean_obj_tag(v_a_2503_) == 0)
{
uint64_t v___x_2546_; 
v___x_2546_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0);
v___y_2509_ = v___x_2546_;
goto v___jp_2508_;
}
else
{
uint64_t v_hash_2547_; 
v_hash_2547_ = lean_ctor_get_uint64(v_a_2503_, sizeof(void*)*2);
v___y_2509_ = v_hash_2547_;
goto v___jp_2508_;
}
v___jp_2508_:
{
uint64_t v___x_2510_; uint64_t v___x_2511_; uint64_t v_fold_2512_; uint64_t v___x_2513_; uint64_t v___x_2514_; uint64_t v___x_2515_; size_t v___x_2516_; size_t v___x_2517_; size_t v___x_2518_; size_t v___x_2519_; size_t v___x_2520_; lean_object* v_bkt_2521_; uint8_t v___x_2522_; 
v___x_2510_ = 32ULL;
v___x_2511_ = lean_uint64_shift_right(v___y_2509_, v___x_2510_);
v_fold_2512_ = lean_uint64_xor(v___y_2509_, v___x_2511_);
v___x_2513_ = 16ULL;
v___x_2514_ = lean_uint64_shift_right(v_fold_2512_, v___x_2513_);
v___x_2515_ = lean_uint64_xor(v_fold_2512_, v___x_2514_);
v___x_2516_ = lean_uint64_to_usize(v___x_2515_);
v___x_2517_ = lean_usize_of_nat(v___x_2507_);
v___x_2518_ = ((size_t)1ULL);
v___x_2519_ = lean_usize_sub(v___x_2517_, v___x_2518_);
v___x_2520_ = lean_usize_land(v___x_2516_, v___x_2519_);
v_bkt_2521_ = lean_array_uget_borrowed(v_buckets_2506_, v___x_2520_);
v___x_2522_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_2503_, v_bkt_2521_);
if (v___x_2522_ == 0)
{
lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2543_; 
lean_inc_ref(v_buckets_2506_);
lean_inc(v_size_2505_);
v_isSharedCheck_2543_ = !lean_is_exclusive(v_m_2502_);
if (v_isSharedCheck_2543_ == 0)
{
lean_object* v_unused_2544_; lean_object* v_unused_2545_; 
v_unused_2544_ = lean_ctor_get(v_m_2502_, 1);
lean_dec(v_unused_2544_);
v_unused_2545_ = lean_ctor_get(v_m_2502_, 0);
lean_dec(v_unused_2545_);
v___x_2524_ = v_m_2502_;
v_isShared_2525_ = v_isSharedCheck_2543_;
goto v_resetjp_2523_;
}
else
{
lean_dec(v_m_2502_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2543_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2526_; lean_object* v_size_x27_2527_; lean_object* v___x_2528_; lean_object* v_buckets_x27_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; uint8_t v___x_2535_; 
v___x_2526_ = lean_unsigned_to_nat(1u);
v_size_x27_2527_ = lean_nat_add(v_size_2505_, v___x_2526_);
lean_dec(v_size_2505_);
lean_inc(v_bkt_2521_);
v___x_2528_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2528_, 0, v_a_2503_);
lean_ctor_set(v___x_2528_, 1, v_b_2504_);
lean_ctor_set(v___x_2528_, 2, v_bkt_2521_);
v_buckets_x27_2529_ = lean_array_uset(v_buckets_2506_, v___x_2520_, v___x_2528_);
v___x_2530_ = lean_unsigned_to_nat(4u);
v___x_2531_ = lean_nat_mul(v_size_x27_2527_, v___x_2530_);
v___x_2532_ = lean_unsigned_to_nat(3u);
v___x_2533_ = lean_nat_div(v___x_2531_, v___x_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_array_get_size(v_buckets_x27_2529_);
v___x_2535_ = lean_nat_dec_le(v___x_2533_, v___x_2534_);
lean_dec(v___x_2533_);
if (v___x_2535_ == 0)
{
lean_object* v_val_2536_; lean_object* v___x_2538_; 
v_val_2536_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6___redArg(v_buckets_x27_2529_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 1, v_val_2536_);
lean_ctor_set(v___x_2524_, 0, v_size_x27_2527_);
v___x_2538_ = v___x_2524_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_size_x27_2527_);
lean_ctor_set(v_reuseFailAlloc_2539_, 1, v_val_2536_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
else
{
lean_object* v___x_2541_; 
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 1, v_buckets_x27_2529_);
lean_ctor_set(v___x_2524_, 0, v_size_x27_2527_);
v___x_2541_ = v___x_2524_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_size_x27_2527_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v_buckets_x27_2529_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
else
{
lean_dec(v_b_2504_);
lean_dec(v_a_2503_);
return v_m_2502_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__1(lean_object* v_as_2548_, size_t v_sz_2549_, size_t v_i_2550_, lean_object* v_b_2551_){
_start:
{
uint8_t v___x_2552_; 
v___x_2552_ = lean_usize_dec_lt(v_i_2550_, v_sz_2549_);
if (v___x_2552_ == 0)
{
return v_b_2551_;
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2554_; lean_object* v_r_2555_; size_t v___x_2556_; size_t v___x_2557_; 
v_a_2553_ = lean_array_uget_borrowed(v_as_2548_, v_i_2550_);
v___x_2554_ = lean_box(0);
lean_inc(v_a_2553_);
v_r_2555_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__0___redArg(v_b_2551_, v_a_2553_, v___x_2554_);
v___x_2556_ = ((size_t)1ULL);
v___x_2557_ = lean_usize_add(v_i_2550_, v___x_2556_);
v_i_2550_ = v___x_2557_;
v_b_2551_ = v_r_2555_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__1___boxed(lean_object* v_as_2559_, lean_object* v_sz_2560_, lean_object* v_i_2561_, lean_object* v_b_2562_){
_start:
{
size_t v_sz_boxed_2563_; size_t v_i_boxed_2564_; lean_object* v_res_2565_; 
v_sz_boxed_2563_ = lean_unbox_usize(v_sz_2560_);
lean_dec(v_sz_2560_);
v_i_boxed_2564_ = lean_unbox_usize(v_i_2561_);
lean_dec(v_i_2561_);
v_res_2565_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__1(v_as_2559_, v_sz_boxed_2563_, v_i_boxed_2564_, v_b_2562_);
lean_dec_ref(v_as_2559_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0(lean_object* v_m_2566_, lean_object* v_l_2567_){
_start:
{
size_t v_sz_2568_; size_t v___x_2569_; lean_object* v___x_2570_; 
v_sz_2568_ = lean_array_size(v_l_2567_);
v___x_2569_ = ((size_t)0ULL);
v___x_2570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__1(v_l_2567_, v_sz_2568_, v___x_2569_, v_m_2566_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0___boxed(lean_object* v_m_2571_, lean_object* v_l_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0(v_m_2571_, v_l_2572_);
lean_dec_ref(v_l_2572_);
return v_res_2573_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg(lean_object* v_m_2574_, lean_object* v_a_2575_){
_start:
{
lean_object* v_buckets_2576_; lean_object* v___x_2577_; uint64_t v___y_2579_; 
v_buckets_2576_ = lean_ctor_get(v_m_2574_, 1);
v___x_2577_ = lean_array_get_size(v_buckets_2576_);
if (lean_obj_tag(v_a_2575_) == 0)
{
uint64_t v___x_2593_; 
v___x_2593_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0);
v___y_2579_ = v___x_2593_;
goto v___jp_2578_;
}
else
{
uint64_t v_hash_2594_; 
v_hash_2594_ = lean_ctor_get_uint64(v_a_2575_, sizeof(void*)*2);
v___y_2579_ = v_hash_2594_;
goto v___jp_2578_;
}
v___jp_2578_:
{
uint64_t v___x_2580_; uint64_t v___x_2581_; uint64_t v_fold_2582_; uint64_t v___x_2583_; uint64_t v___x_2584_; uint64_t v___x_2585_; size_t v___x_2586_; size_t v___x_2587_; size_t v___x_2588_; size_t v___x_2589_; size_t v___x_2590_; lean_object* v___x_2591_; uint8_t v___x_2592_; 
v___x_2580_ = 32ULL;
v___x_2581_ = lean_uint64_shift_right(v___y_2579_, v___x_2580_);
v_fold_2582_ = lean_uint64_xor(v___y_2579_, v___x_2581_);
v___x_2583_ = 16ULL;
v___x_2584_ = lean_uint64_shift_right(v_fold_2582_, v___x_2583_);
v___x_2585_ = lean_uint64_xor(v_fold_2582_, v___x_2584_);
v___x_2586_ = lean_uint64_to_usize(v___x_2585_);
v___x_2587_ = lean_usize_of_nat(v___x_2577_);
v___x_2588_ = ((size_t)1ULL);
v___x_2589_ = lean_usize_sub(v___x_2587_, v___x_2588_);
v___x_2590_ = lean_usize_land(v___x_2586_, v___x_2589_);
v___x_2591_ = lean_array_uget_borrowed(v_buckets_2576_, v___x_2590_);
v___x_2592_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_2575_, v___x_2591_);
return v___x_2592_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg___boxed(lean_object* v_m_2595_, lean_object* v_a_2596_){
_start:
{
uint8_t v_res_2597_; lean_object* v_r_2598_; 
v_res_2597_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg(v_m_2595_, v_a_2596_);
lean_dec(v_a_2596_);
lean_dec_ref(v_m_2595_);
v_r_2598_ = lean_box(v_res_2597_);
return v_r_2598_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7___redArg(lean_object* v_a_2599_, lean_object* v_b_2600_, lean_object* v_x_2601_){
_start:
{
if (lean_obj_tag(v_x_2601_) == 0)
{
lean_dec(v_b_2600_);
lean_dec(v_a_2599_);
return v_x_2601_;
}
else
{
lean_object* v_key_2602_; lean_object* v_value_2603_; lean_object* v_tail_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2616_; 
v_key_2602_ = lean_ctor_get(v_x_2601_, 0);
v_value_2603_ = lean_ctor_get(v_x_2601_, 1);
v_tail_2604_ = lean_ctor_get(v_x_2601_, 2);
v_isSharedCheck_2616_ = !lean_is_exclusive(v_x_2601_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2606_ = v_x_2601_;
v_isShared_2607_ = v_isSharedCheck_2616_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_tail_2604_);
lean_inc(v_value_2603_);
lean_inc(v_key_2602_);
lean_dec(v_x_2601_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2616_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
uint8_t v___x_2608_; 
v___x_2608_ = lean_name_eq(v_key_2602_, v_a_2599_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; lean_object* v___x_2611_; 
v___x_2609_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7___redArg(v_a_2599_, v_b_2600_, v_tail_2604_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 2, v___x_2609_);
v___x_2611_ = v___x_2606_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_key_2602_);
lean_ctor_set(v_reuseFailAlloc_2612_, 1, v_value_2603_);
lean_ctor_set(v_reuseFailAlloc_2612_, 2, v___x_2609_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
else
{
lean_object* v___x_2614_; 
lean_dec(v_value_2603_);
lean_dec(v_key_2602_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 1, v_b_2600_);
lean_ctor_set(v___x_2606_, 0, v_a_2599_);
v___x_2614_ = v___x_2606_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2599_);
lean_ctor_set(v_reuseFailAlloc_2615_, 1, v_b_2600_);
lean_ctor_set(v_reuseFailAlloc_2615_, 2, v_tail_2604_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3___redArg(lean_object* v_m_2617_, lean_object* v_a_2618_, lean_object* v_b_2619_){
_start:
{
lean_object* v_size_2620_; lean_object* v_buckets_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2667_; 
v_size_2620_ = lean_ctor_get(v_m_2617_, 0);
v_buckets_2621_ = lean_ctor_get(v_m_2617_, 1);
v_isSharedCheck_2667_ = !lean_is_exclusive(v_m_2617_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2623_ = v_m_2617_;
v_isShared_2624_ = v_isSharedCheck_2667_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_buckets_2621_);
lean_inc(v_size_2620_);
lean_dec(v_m_2617_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2667_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2625_; uint64_t v___y_2627_; 
v___x_2625_ = lean_array_get_size(v_buckets_2621_);
if (lean_obj_tag(v_a_2618_) == 0)
{
uint64_t v___x_2665_; 
v___x_2665_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0);
v___y_2627_ = v___x_2665_;
goto v___jp_2626_;
}
else
{
uint64_t v_hash_2666_; 
v_hash_2666_ = lean_ctor_get_uint64(v_a_2618_, sizeof(void*)*2);
v___y_2627_ = v_hash_2666_;
goto v___jp_2626_;
}
v___jp_2626_:
{
uint64_t v___x_2628_; uint64_t v___x_2629_; uint64_t v_fold_2630_; uint64_t v___x_2631_; uint64_t v___x_2632_; uint64_t v___x_2633_; size_t v___x_2634_; size_t v___x_2635_; size_t v___x_2636_; size_t v___x_2637_; size_t v___x_2638_; lean_object* v_bkt_2639_; uint8_t v___x_2640_; 
v___x_2628_ = 32ULL;
v___x_2629_ = lean_uint64_shift_right(v___y_2627_, v___x_2628_);
v_fold_2630_ = lean_uint64_xor(v___y_2627_, v___x_2629_);
v___x_2631_ = 16ULL;
v___x_2632_ = lean_uint64_shift_right(v_fold_2630_, v___x_2631_);
v___x_2633_ = lean_uint64_xor(v_fold_2630_, v___x_2632_);
v___x_2634_ = lean_uint64_to_usize(v___x_2633_);
v___x_2635_ = lean_usize_of_nat(v___x_2625_);
v___x_2636_ = ((size_t)1ULL);
v___x_2637_ = lean_usize_sub(v___x_2635_, v___x_2636_);
v___x_2638_ = lean_usize_land(v___x_2634_, v___x_2637_);
v_bkt_2639_ = lean_array_uget_borrowed(v_buckets_2621_, v___x_2638_);
v___x_2640_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_2618_, v_bkt_2639_);
if (v___x_2640_ == 0)
{
lean_object* v___x_2641_; lean_object* v_size_x27_2642_; lean_object* v___x_2643_; lean_object* v_buckets_x27_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; uint8_t v___x_2650_; 
v___x_2641_ = lean_unsigned_to_nat(1u);
v_size_x27_2642_ = lean_nat_add(v_size_2620_, v___x_2641_);
lean_dec(v_size_2620_);
lean_inc(v_bkt_2639_);
v___x_2643_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2643_, 0, v_a_2618_);
lean_ctor_set(v___x_2643_, 1, v_b_2619_);
lean_ctor_set(v___x_2643_, 2, v_bkt_2639_);
v_buckets_x27_2644_ = lean_array_uset(v_buckets_2621_, v___x_2638_, v___x_2643_);
v___x_2645_ = lean_unsigned_to_nat(4u);
v___x_2646_ = lean_nat_mul(v_size_x27_2642_, v___x_2645_);
v___x_2647_ = lean_unsigned_to_nat(3u);
v___x_2648_ = lean_nat_div(v___x_2646_, v___x_2647_);
lean_dec(v___x_2646_);
v___x_2649_ = lean_array_get_size(v_buckets_x27_2644_);
v___x_2650_ = lean_nat_dec_le(v___x_2648_, v___x_2649_);
lean_dec(v___x_2648_);
if (v___x_2650_ == 0)
{
lean_object* v_val_2651_; lean_object* v___x_2653_; 
v_val_2651_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6___redArg(v_buckets_x27_2644_);
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 1, v_val_2651_);
lean_ctor_set(v___x_2623_, 0, v_size_x27_2642_);
v___x_2653_ = v___x_2623_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_size_x27_2642_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v_val_2651_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
else
{
lean_object* v___x_2656_; 
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 1, v_buckets_x27_2644_);
lean_ctor_set(v___x_2623_, 0, v_size_x27_2642_);
v___x_2656_ = v___x_2623_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_size_x27_2642_);
lean_ctor_set(v_reuseFailAlloc_2657_, 1, v_buckets_x27_2644_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
else
{
lean_object* v___x_2658_; lean_object* v_buckets_x27_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2663_; 
lean_inc(v_bkt_2639_);
v___x_2658_ = lean_box(0);
v_buckets_x27_2659_ = lean_array_uset(v_buckets_2621_, v___x_2638_, v___x_2658_);
v___x_2660_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7___redArg(v_a_2618_, v_b_2619_, v_bkt_2639_);
v___x_2661_ = lean_array_uset(v_buckets_x27_2659_, v___x_2638_, v___x_2660_);
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 1, v___x_2661_);
v___x_2663_ = v___x_2623_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_size_2620_);
lean_ctor_set(v_reuseFailAlloc_2664_, 1, v___x_2661_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2671_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__2));
v___x_2672_ = lean_unsigned_to_nat(4u);
v___x_2673_ = lean_unsigned_to_nat(240u);
v___x_2674_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__1));
v___x_2675_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__0));
v___x_2676_ = l_mkPanicMessageWithDecl(v___x_2675_, v___x_2674_, v___x_2673_, v___x_2672_, v___x_2671_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg(lean_object* v___x_2677_, lean_object* v_as_x27_2678_, lean_object* v_b_2679_){
_start:
{
if (lean_obj_tag(v_as_x27_2678_) == 0)
{
return v_b_2679_;
}
else
{
lean_object* v_head_2680_; lean_object* v_tail_2681_; lean_object* v_fst_2682_; lean_object* v_snd_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2704_; 
v_head_2680_ = lean_ctor_get(v_as_x27_2678_, 0);
lean_inc(v_head_2680_);
v_tail_2681_ = lean_ctor_get(v_as_x27_2678_, 1);
lean_inc(v_tail_2681_);
lean_dec_ref(v_as_x27_2678_);
v_fst_2682_ = lean_ctor_get(v_b_2679_, 0);
v_snd_2683_ = lean_ctor_get(v_b_2679_, 1);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_b_2679_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2685_ = v_b_2679_;
v_isShared_2686_ = v_isSharedCheck_2704_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_snd_2683_);
lean_inc(v_fst_2682_);
lean_dec(v_b_2679_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2704_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v_map_2688_; uint8_t v___x_2702_; 
v___x_2702_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg(v___x_2677_, v_head_2680_);
if (v___x_2702_ == 0)
{
lean_dec(v_head_2680_);
v_map_2688_ = v_fst_2682_;
goto v___jp_2687_;
}
else
{
lean_object* v___x_2703_; 
lean_inc(v_snd_2683_);
v___x_2703_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3___redArg(v_fst_2682_, v_head_2680_, v_snd_2683_);
v_map_2688_ = v___x_2703_;
goto v___jp_2687_;
}
v___jp_2687_:
{
lean_object* v___x_2689_; uint8_t v___x_2690_; 
v___x_2689_ = lean_unsigned_to_nat(0u);
v___x_2690_ = lean_nat_dec_eq(v_snd_2683_, v___x_2689_);
if (v___x_2690_ == 0)
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2694_; 
v___x_2691_ = lean_unsigned_to_nat(1u);
v___x_2692_ = lean_nat_sub(v_snd_2683_, v___x_2691_);
lean_dec(v_snd_2683_);
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 1, v___x_2692_);
lean_ctor_set(v___x_2685_, 0, v_map_2688_);
v___x_2694_ = v___x_2685_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_map_2688_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v___x_2692_);
v___x_2694_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
v_as_x27_2678_ = v_tail_2681_;
v_b_2679_ = v___x_2694_;
goto _start;
}
}
else
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
lean_dec_ref(v_map_2688_);
lean_del_object(v___x_2685_);
lean_dec(v_snd_2683_);
v___x_2697_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3);
v___x_2698_ = l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1(v___x_2697_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; 
lean_dec(v_tail_2681_);
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
lean_dec_ref(v___x_2698_);
return v_a_2699_;
}
else
{
lean_object* v_a_2700_; 
v_a_2700_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2700_);
lean_dec_ref(v___x_2698_);
v_as_x27_2678_ = v_tail_2681_;
v_b_2679_ = v_a_2700_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___boxed(lean_object* v___x_2705_, lean_object* v_as_x27_2706_, lean_object* v_b_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg(v___x_2705_, v_as_x27_2706_, v_b_2707_);
lean_dec_ref(v___x_2705_);
return v_res_2708_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0(void){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2709_ = lean_box(0);
v___x_2710_ = lean_unsigned_to_nat(16u);
v___x_2711_ = lean_mk_array(v___x_2710_, v___x_2709_);
return v___x_2711_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1(void){
_start:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2712_ = lean_obj_once(&l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0, &l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0_once, _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0);
v___x_2713_ = lean_unsigned_to_nat(0u);
v___x_2714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
lean_ctor_set(v___x_2714_, 1, v___x_2712_);
return v___x_2714_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3(void){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2716_ = ((lean_object*)(l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__2));
v___x_2717_ = lean_unsigned_to_nat(2u);
v___x_2718_ = lean_unsigned_to_nat(242u);
v___x_2719_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__1));
v___x_2720_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__0));
v___x_2721_ = l_mkPanicMessageWithDecl(v___x_2720_, v___x_2719_, v___x_2718_, v___x_2717_, v___x_2716_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureDeclIndices(lean_object* v_env_2722_, lean_object* v_targets_2723_){
_start:
{
lean_object* v___x_2724_; lean_object* v_asyncMode_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v_fst_2729_; lean_object* v_snd_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2759_; 
v___x_2724_ = l_Lean_Compiler_LCNF_declOrderExt;
v_asyncMode_2725_ = lean_ctor_get(v___x_2724_, 2);
lean_inc(v_asyncMode_2725_);
v___x_2726_ = ((lean_object*)(l_Lean_Compiler_LCNF_isDeclTransparent___closed__0));
v___x_2727_ = lean_box(0);
v___x_2728_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2726_, v___x_2724_, v_env_2722_, v_asyncMode_2725_, v___x_2727_);
lean_dec(v_asyncMode_2725_);
v_fst_2729_ = lean_ctor_get(v___x_2728_, 0);
v_snd_2730_ = lean_ctor_get(v___x_2728_, 1);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2732_ = v___x_2728_;
v_isShared_2733_ = v_isSharedCheck_2759_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_snd_2730_);
lean_inc(v_fst_2729_);
lean_dec(v___x_2728_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2759_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___y_2735_; 
if (lean_obj_tag(v_snd_2730_) == 0)
{
lean_object* v_size_2757_; 
v_size_2757_ = lean_ctor_get(v_snd_2730_, 0);
lean_inc(v_size_2757_);
lean_dec_ref(v_snd_2730_);
v___y_2735_ = v_size_2757_;
goto v___jp_2734_;
}
else
{
lean_object* v___x_2758_; 
v___x_2758_ = lean_unsigned_to_nat(0u);
v___y_2735_ = v___x_2758_;
goto v___jp_2734_;
}
v___jp_2734_:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v_map_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2748_; 
v___x_2736_ = lean_unsigned_to_nat(0u);
v___x_2737_ = lean_unsigned_to_nat(4u);
v___x_2738_ = lean_nat_mul(v___y_2735_, v___x_2737_);
v___x_2739_ = lean_unsigned_to_nat(3u);
v___x_2740_ = lean_nat_div(v___x_2738_, v___x_2739_);
lean_dec(v___x_2738_);
v___x_2741_ = l_Nat_nextPowerOfTwo(v___x_2740_);
lean_dec(v___x_2740_);
v___x_2742_ = lean_box(0);
v___x_2743_ = lean_mk_array(v___x_2741_, v___x_2742_);
v_map_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_map_2744_, 0, v___x_2736_);
lean_ctor_set(v_map_2744_, 1, v___x_2743_);
v___x_2745_ = lean_obj_once(&l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1, &l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1_once, _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1);
v___x_2746_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0(v___x_2745_, v_targets_2723_);
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 1, v___y_2735_);
lean_ctor_set(v___x_2732_, 0, v_map_2744_);
v___x_2748_ = v___x_2732_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_map_2744_);
lean_ctor_set(v_reuseFailAlloc_2756_, 1, v___y_2735_);
v___x_2748_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
lean_object* v___x_2749_; lean_object* v_fst_2750_; lean_object* v_size_2751_; lean_object* v___x_2752_; uint8_t v___x_2753_; 
v___x_2749_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg(v___x_2746_, v_fst_2729_, v___x_2748_);
lean_dec_ref(v___x_2746_);
v_fst_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_fst_2750_);
lean_dec_ref(v___x_2749_);
v_size_2751_ = lean_ctor_get(v_fst_2750_, 0);
v___x_2752_ = lean_array_get_size(v_targets_2723_);
v___x_2753_ = lean_nat_dec_eq(v_size_2751_, v___x_2752_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2754_; lean_object* v___x_2755_; 
lean_dec(v_fst_2750_);
v___x_2754_ = lean_obj_once(&l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3, &l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3_once, _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3);
v___x_2755_ = l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__5(v___x_2754_);
return v___x_2755_;
}
else
{
return v_fst_2750_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureDeclIndices___boxed(lean_object* v_env_2760_, lean_object* v_targets_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l_Lean_Compiler_LCNF_getImpureDeclIndices(v_env_2760_, v_targets_2761_);
lean_dec_ref(v_targets_2761_);
return v_res_2762_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2(lean_object* v_00_u03b2_2763_, lean_object* v_m_2764_, lean_object* v_a_2765_){
_start:
{
uint8_t v___x_2766_; 
v___x_2766_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg(v_m_2764_, v_a_2765_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___boxed(lean_object* v_00_u03b2_2767_, lean_object* v_m_2768_, lean_object* v_a_2769_){
_start:
{
uint8_t v_res_2770_; lean_object* v_r_2771_; 
v_res_2770_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2(v_00_u03b2_2767_, v_m_2768_, v_a_2769_);
lean_dec(v_a_2769_);
lean_dec_ref(v_m_2768_);
v_r_2771_ = lean_box(v_res_2770_);
return v_r_2771_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3(lean_object* v_00_u03b2_2772_, lean_object* v_m_2773_, lean_object* v_a_2774_, lean_object* v_b_2775_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3___redArg(v_m_2773_, v_a_2774_, v_b_2775_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4(lean_object* v___x_2777_, lean_object* v_as_2778_, lean_object* v_as_x27_2779_, lean_object* v_b_2780_, lean_object* v_a_2781_){
_start:
{
lean_object* v___x_2782_; 
v___x_2782_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg(v___x_2777_, v_as_x27_2779_, v_b_2780_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___boxed(lean_object* v___x_2783_, lean_object* v_as_2784_, lean_object* v_as_x27_2785_, lean_object* v_b_2786_, lean_object* v_a_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4(v___x_2783_, v_as_2784_, v_as_x27_2785_, v_b_2786_, v_a_2787_);
lean_dec(v_as_2784_);
lean_dec_ref(v___x_2783_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__0(lean_object* v_00_u03b2_2789_, lean_object* v_m_2790_, lean_object* v_a_2791_, lean_object* v_b_2792_){
_start:
{
lean_object* v___x_2793_; 
v___x_2793_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__0___redArg(v_m_2790_, v_a_2791_, v_b_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4(lean_object* v_00_u03b2_2794_, lean_object* v_a_2795_, lean_object* v_x_2796_){
_start:
{
uint8_t v___x_2797_; 
v___x_2797_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_2795_, v_x_2796_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2798_, lean_object* v_a_2799_, lean_object* v_x_2800_){
_start:
{
uint8_t v_res_2801_; lean_object* v_r_2802_; 
v_res_2801_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4(v_00_u03b2_2798_, v_a_2799_, v_x_2800_);
lean_dec(v_x_2800_);
lean_dec(v_a_2799_);
v_r_2802_ = lean_box(v_res_2801_);
return v_r_2802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6(lean_object* v_00_u03b2_2803_, lean_object* v_data_2804_){
_start:
{
lean_object* v___x_2805_; 
v___x_2805_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6___redArg(v_data_2804_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7(lean_object* v_00_u03b2_2806_, lean_object* v_a_2807_, lean_object* v_b_2808_, lean_object* v_x_2809_){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7___redArg(v_a_2807_, v_b_2808_, v_x_2809_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_2811_, lean_object* v_i_2812_, lean_object* v_source_2813_, lean_object* v_target_2814_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8___redArg(v_i_2812_, v_source_2813_, v_target_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_2816_, lean_object* v_x_2817_, lean_object* v_x_2818_){
_start:
{
lean_object* v___x_2819_; 
v___x_2819_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8_spec__10___redArg(v_x_2817_, v_x_2818_);
return v___x_2819_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PublicDeclsExt(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_baseExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_baseExt);
lean_dec_ref(res);
res = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_monoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_monoExt);
lean_dec_ref(res);
res = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_impureExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_impureExt);
lean_dec_ref(res);
res = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_impureSigExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_impureSigExt);
lean_dec_ref(res);
res = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2_();
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
