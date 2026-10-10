// Lean compiler output
// Module: Lean.Compiler.LCNF.ResetReuse
// Imports: public import Lean.Compiler.LCNF.CompilerM public import Lean.Compiler.LCNF.PassManager import Lean.Compiler.LCNF.LiveVars import Lean.Compiler.LCNF.DependsOn import Lean.Compiler.LCNF.PhaseExt import Lean.Compiler.LCNF.PropagateBorrow
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
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(uint8_t, lean_object*);
lean_object* l_Lean_instSingletonFVarIdFVarIdSet___lam__0(lean_object*);
uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_CodeDecl_dependsOn(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(uint8_t, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_isFVarLiveIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_applyOwnedness(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t l_Lean_Compiler_LCNF_instBEqOwnedness_beq(uint8_t, uint8_t);
uint8_t l_Lean_Compiler_LCNF_CtorInfo_isScalar(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0(lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateContImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.LCNF.Basic"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "_private.Lean.Compiler.LCNF.ResetReuse.0.Lean.Compiler.LCNF.S.go"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Compiler.LCNF.ResetReuse"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tobj"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__2_value),LEAN_SCALAR_PTR_LITERAL(25, 168, 138, 20, 203, 141, 233, 12)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__3_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "_private.Lean.Compiler.LCNF.ResetReuse.0.Lean.Compiler.LCNF.D.go"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "_private.Lean.Compiler.LCNF.ResetReuse.0.Lean.Compiler.LCNF.Code.insertResetReuse"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(uint8_t, lean_object*, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 100, .m_capacity = 100, .m_length = 99, .m_data = "_private.Lean.Compiler.LCNF.ResetReuse.0.Lean.Compiler.LCNF.Decl.insertResetReuseCore.collectResets"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_insertResetReuse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "resetReuse"};
static const lean_object* l_Lean_Compiler_LCNF_insertResetReuse___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_insertResetReuse___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_insertResetReuse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_insertResetReuse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 201, 93, 114, 179, 16, 247, 72)}};
static const lean_object* l_Lean_Compiler_LCNF_insertResetReuse___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_insertResetReuse___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_insertResetReuse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_insertResetReuse___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_insertResetReuse___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_insertResetReuse___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_insertResetReuse___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_insertResetReuse;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_insertResetReuse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 22, 75, 214, 119, 69, 48, 225)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ResetReuse"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(16, 165, 194, 12, 198, 157, 117, 65)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(105, 150, 117, 254, 63, 70, 178, 234)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(44, 242, 201, 181, 138, 172, 149, 255)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(182, 154, 112, 50, 132, 225, 68, 23)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(31, 182, 243, 139, 183, 248, 56, 98)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(190, 130, 185, 126, 60, 87, 109, 106)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 224, 225, 246, 174, 48, 45, 78)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(146, 47, 104, 191, 68, 113, 248, 179)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(96, 193, 129, 108, 61, 130, 124, 18)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(217, 251, 249, 254, 208, 86, 150, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(8, 85, 80, 162, 8, 82, 178, 101)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2____boxed(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(lean_object* v_c_u2081_1_, lean_object* v_c_u2082_2_, lean_object* v_a_3_){
_start:
{
lean_object* v_name_5_; lean_object* v_size_6_; lean_object* v_usize_7_; lean_object* v_ssize_8_; lean_object* v_name_9_; lean_object* v_size_10_; lean_object* v_usize_11_; lean_object* v_ssize_12_; uint8_t v___x_13_; 
v_name_5_ = lean_ctor_get(v_c_u2081_1_, 0);
v_size_6_ = lean_ctor_get(v_c_u2081_1_, 2);
v_usize_7_ = lean_ctor_get(v_c_u2081_1_, 3);
v_ssize_8_ = lean_ctor_get(v_c_u2081_1_, 4);
v_name_9_ = lean_ctor_get(v_c_u2082_2_, 0);
v_size_10_ = lean_ctor_get(v_c_u2082_2_, 2);
v_usize_11_ = lean_ctor_get(v_c_u2082_2_, 3);
v_ssize_12_ = lean_ctor_get(v_c_u2082_2_, 4);
v___x_13_ = lean_nat_dec_eq(v_size_6_, v_size_10_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_box(v___x_13_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
else
{
uint8_t v___x_16_; 
v___x_16_ = lean_nat_dec_eq(v_usize_7_, v_usize_11_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lean_box(v___x_16_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
else
{
uint8_t v___x_19_; 
v___x_19_ = lean_nat_dec_eq(v_ssize_8_, v_ssize_12_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_box(v___x_19_);
v___x_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
return v___x_21_;
}
else
{
uint8_t v_relaxedReuse_22_; 
v_relaxedReuse_22_ = lean_ctor_get_uint8(v_a_3_, sizeof(void*)*2);
if (v_relaxedReuse_22_ == 0)
{
lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_23_ = l_Lean_Name_getPrefix(v_name_5_);
v___x_24_ = l_Lean_Name_getPrefix(v_name_9_);
v___x_25_ = lean_name_eq(v___x_23_, v___x_24_);
lean_dec(v___x_24_);
lean_dec(v___x_23_);
v___x_26_ = lean_box(v___x_25_);
v___x_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
return v___x_27_;
}
else
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_box(v_relaxedReuse_22_);
v___x_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_u2081_1_ = stack[0].m_obj;
lean_object* v_c_u2082_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_res_30_;
v_res_30_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(v_c_u2081_1_, v_c_u2082_2_, v_a_3_);
stack->m_obj
 = v_res_30_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg___boxed(lean_object* v_c_u2081_31_, lean_object* v_c_u2082_32_, lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(v_c_u2081_31_, v_c_u2082_32_, v_a_33_);
lean_dec_ref(v_a_33_);
lean_dec_ref(v_c_u2082_32_);
lean_dec_ref(v_c_u2081_31_);
return v_res_35_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse(lean_object* v_c_u2081_36_, lean_object* v_c_u2082_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(v_c_u2081_36_, v_c_u2082_37_, v_a_38_);
return v___x_44_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_u2081_36_ = stack[0].m_obj;
lean_object* v_c_u2082_37_ = stack[1].m_obj;
lean_object* v_a_38_ = stack[2].m_obj;
lean_object* v_a_39_ = stack[3].m_obj;
lean_object* v_a_40_ = stack[4].m_obj;
lean_object* v_a_41_ = stack[5].m_obj;
lean_object* v_a_42_ = stack[6].m_obj;
lean_object* v_res_45_;
v_res_45_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse(v_c_u2081_36_, v_c_u2082_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___boxed(lean_object* v_c_u2081_46_, lean_object* v_c_u2082_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse(v_c_u2081_46_, v_c_u2082_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_c_u2082_47_);
lean_dec_ref(v_c_u2081_46_);
return v_res_54_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0(lean_object* v_msg_56_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0);
v___x_58_ = lean_panic_fn_borrowed(v___x_57_, v_msg_56_);
return v___x_58_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0(void){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_instMonadEIO___redArg();
return v___x_59_;
}
}
lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(lean_object* v_msg_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v_toApplicative_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_108_; 
v___x_69_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0);
v___x_70_ = l_StateRefT_x27_instMonad___redArg(v___x_69_);
v_toApplicative_71_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_108_ == 0)
{
lean_object* v_unused_109_; 
v_unused_109_ = lean_ctor_get(v___x_70_, 1);
lean_dec(v_unused_109_);
v___x_73_ = v___x_70_;
v_isShared_74_ = v_isSharedCheck_108_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_toApplicative_71_);
lean_dec(v___x_70_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_108_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v_toFunctor_75_; lean_object* v_toSeq_76_; lean_object* v_toSeqLeft_77_; lean_object* v_toSeqRight_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_106_; 
v_toFunctor_75_ = lean_ctor_get(v_toApplicative_71_, 0);
v_toSeq_76_ = lean_ctor_get(v_toApplicative_71_, 2);
v_toSeqLeft_77_ = lean_ctor_get(v_toApplicative_71_, 3);
v_toSeqRight_78_ = lean_ctor_get(v_toApplicative_71_, 4);
v_isSharedCheck_106_ = !lean_is_exclusive(v_toApplicative_71_);
if (v_isSharedCheck_106_ == 0)
{
lean_object* v_unused_107_; 
v_unused_107_ = lean_ctor_get(v_toApplicative_71_, 1);
lean_dec(v_unused_107_);
v___x_80_ = v_toApplicative_71_;
v_isShared_81_ = v_isSharedCheck_106_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_toSeqRight_78_);
lean_inc(v_toSeqLeft_77_);
lean_inc(v_toSeq_76_);
lean_inc(v_toFunctor_75_);
lean_dec(v_toApplicative_71_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_106_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___f_82_; lean_object* v___f_83_; lean_object* v___f_84_; lean_object* v___f_85_; lean_object* v___x_86_; lean_object* v___f_87_; lean_object* v___f_88_; lean_object* v___f_89_; lean_object* v___x_91_; 
v___f_82_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1));
v___f_83_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2));
lean_inc_ref(v_toFunctor_75_);
v___f_84_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_84_, 0, v_toFunctor_75_);
v___f_85_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_85_, 0, v_toFunctor_75_);
v___x_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_86_, 0, v___f_84_);
lean_ctor_set(v___x_86_, 1, v___f_85_);
v___f_87_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_87_, 0, v_toSeqRight_78_);
v___f_88_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_88_, 0, v_toSeqLeft_77_);
v___f_89_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_89_, 0, v_toSeq_76_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 4, v___f_87_);
lean_ctor_set(v___x_80_, 3, v___f_88_);
lean_ctor_set(v___x_80_, 2, v___f_89_);
lean_ctor_set(v___x_80_, 1, v___f_82_);
lean_ctor_set(v___x_80_, 0, v___x_86_);
v___x_91_ = v___x_80_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_86_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v___f_82_);
lean_ctor_set(v_reuseFailAlloc_105_, 2, v___f_89_);
lean_ctor_set(v_reuseFailAlloc_105_, 3, v___f_88_);
lean_ctor_set(v_reuseFailAlloc_105_, 4, v___f_87_);
v___x_91_ = v_reuseFailAlloc_105_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
lean_object* v___x_93_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 1, v___f_83_);
lean_ctor_set(v___x_73_, 0, v___x_91_);
v___x_93_ = v___x_73_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_91_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v___f_83_);
v___x_93_ = v_reuseFailAlloc_104_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___f_100_; lean_object* v___f_101_; lean_object* v___x_3636__overap_102_; lean_object* v___x_103_; 
v___x_94_ = l_StateRefT_x27_instMonad___redArg(v___x_93_);
v___x_95_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0);
v___x_96_ = 0;
v___x_97_ = lean_box(v___x_96_);
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_95_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v___x_99_ = l_instInhabitedOfMonad___redArg(v___x_94_, v___x_98_);
v___f_100_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_100_, 0, v___x_99_);
v___f_101_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_101_, 0, v___f_100_);
v___x_3636__overap_102_ = lean_panic_fn_borrowed(v___f_101_, v_msg_62_);
lean_dec_ref(v___f_101_);
lean_inc(v___y_67_);
lean_inc_ref(v___y_66_);
lean_inc(v___y_65_);
lean_inc_ref(v___y_64_);
lean_inc_ref(v___y_63_);
v___x_103_ = lean_apply_6(v___x_3636__overap_102_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, lean_box(0));
return v___x_103_;
}
}
}
}
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_62_ = stack[0].m_obj;
lean_object* v___y_63_ = stack[1].m_obj;
lean_object* v___y_64_ = stack[2].m_obj;
lean_object* v___y_65_ = stack[3].m_obj;
lean_object* v___y_66_ = stack[4].m_obj;
lean_object* v___y_67_ = stack[5].m_obj;
lean_object* v_res_110_;
v_res_110_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(v_msg_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
stack->m_obj
 = v_res_110_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___boxed(lean_object* v_msg_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(v_msg_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec_ref(v___y_112_);
return v_res_118_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(lean_object* v_as_119_, size_t v_i_120_, size_t v_stop_121_){
_start:
{
uint8_t v___x_122_; 
v___x_122_ = lean_usize_dec_eq(v_i_120_, v_stop_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = lean_array_uget_borrowed(v_as_119_, v_i_120_);
v___x_124_ = lean_unbox(v___x_123_);
if (v___x_124_ == 0)
{
size_t v___x_125_; size_t v___x_126_; 
v___x_125_ = ((size_t)1ULL);
v___x_126_ = lean_usize_add(v_i_120_, v___x_125_);
v_i_120_ = v___x_126_;
goto _start;
}
else
{
uint8_t v___x_128_; 
v___x_128_ = lean_unbox(v___x_123_);
return v___x_128_;
}
}
else
{
uint8_t v___x_129_; 
v___x_129_ = 0;
return v___x_129_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_119_ = stack[0].m_obj;
size_t v_i_120_ = stack[1].m_num;
size_t v_stop_121_ = stack[2].m_num;
uint8_t v_res_130_;
v_res_130_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(v_as_119_, v_i_120_, v_stop_121_);
stack->m_num = v_res_130_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2___boxed(lean_object* v_as_131_, lean_object* v_i_132_, lean_object* v_stop_133_){
_start:
{
size_t v_i_boxed_134_; size_t v_stop_boxed_135_; uint8_t v_res_136_; lean_object* v_r_137_; 
v_i_boxed_134_ = lean_unbox_usize(v_i_132_);
lean_dec(v_i_132_);
v_stop_boxed_135_ = lean_unbox_usize(v_stop_133_);
lean_dec(v_stop_133_);
v_res_136_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(v_as_131_, v_i_boxed_134_, v_stop_boxed_135_);
lean_dec_ref(v_as_131_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_141_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_142_ = lean_unsigned_to_nat(9u);
v___x_143_ = lean_unsigned_to_nat(642u);
v___x_144_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__1));
v___x_145_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__0));
v___x_146_ = l_mkPanicMessageWithDecl(v___x_145_, v___x_144_, v___x_143_, v___x_142_, v___x_141_);
return v___x_146_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_149_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_150_ = lean_unsigned_to_nat(61u);
v___x_151_ = lean_unsigned_to_nat(125u);
v___x_152_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__5));
v___x_153_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_154_ = l_mkPanicMessageWithDecl(v___x_153_, v___x_152_, v___x_151_, v___x_150_, v___x_149_);
return v___x_154_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(lean_object* v_info_155_, lean_object* v_w_156_, lean_object* v_c_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
uint8_t v___y_165_; lean_object* v___y_166_; lean_object* v_k_171_; lean_object* v___y_172_; lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___y_175_; lean_object* v___y_176_; 
switch(lean_obj_tag(v_c_157_))
{
case 0:
{
lean_object* v_decl_391_; lean_object* v_value_392_; 
v_decl_391_ = lean_ctor_get(v_c_157_, 0);
lean_inc_ref(v_decl_391_);
v_value_392_ = lean_ctor_get(v_decl_391_, 3);
lean_inc(v_value_392_);
if (lean_obj_tag(v_value_392_) == 5)
{
lean_object* v_k_393_; lean_object* v_fvarId_394_; lean_object* v_binderName_395_; lean_object* v_type_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_451_; 
v_k_393_ = lean_ctor_get(v_c_157_, 1);
v_fvarId_394_ = lean_ctor_get(v_decl_391_, 0);
v_binderName_395_ = lean_ctor_get(v_decl_391_, 1);
v_type_396_ = lean_ctor_get(v_decl_391_, 2);
v_isSharedCheck_451_ = !lean_is_exclusive(v_decl_391_);
if (v_isSharedCheck_451_ == 0)
{
lean_object* v_unused_452_; 
v_unused_452_ = lean_ctor_get(v_decl_391_, 3);
lean_dec(v_unused_452_);
v___x_398_ = v_decl_391_;
v_isShared_399_ = v_isSharedCheck_451_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_type_396_);
lean_inc(v_binderName_395_);
lean_inc(v_fvarId_394_);
lean_dec(v_decl_391_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_451_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v_i_400_; lean_object* v_args_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_450_; 
v_i_400_ = lean_ctor_get(v_value_392_, 0);
v_args_401_ = lean_ctor_get(v_value_392_, 1);
v_isSharedCheck_450_ = !lean_is_exclusive(v_value_392_);
if (v_isSharedCheck_450_ == 0)
{
v___x_403_ = v_value_392_;
v_isShared_404_ = v_isSharedCheck_450_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_args_401_);
lean_inc(v_i_400_);
lean_dec(v_value_392_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_450_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
uint8_t v___x_405_; lean_object* v___x_407_; 
v___x_405_ = 1;
lean_inc_ref(v_args_401_);
lean_inc_ref(v_i_400_);
if (v_isShared_404_ == 0)
{
v___x_407_ = v___x_403_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_i_400_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v_args_401_);
v___x_407_ = v_reuseFailAlloc_449_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v___x_409_; 
lean_inc_ref(v_type_396_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 3, v___x_407_);
v___x_409_ = v___x_398_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_fvarId_394_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_binderName_395_);
lean_ctor_set(v_reuseFailAlloc_448_, 2, v_type_396_);
lean_ctor_set(v_reuseFailAlloc_448_, 3, v___x_407_);
v___x_409_ = v_reuseFailAlloc_448_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_410_; 
v___x_410_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(v_info_155_, v_i_400_, v_a_158_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; uint8_t v___y_413_; uint8_t v___x_434_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_411_);
lean_dec_ref_known(v___x_410_, 1);
v___x_434_ = lean_unbox(v_a_411_);
if (v___x_434_ == 0)
{
lean_dec(v_a_411_);
lean_dec_ref(v___x_409_);
lean_dec_ref(v_args_401_);
lean_dec_ref(v_i_400_);
lean_dec_ref(v_type_396_);
lean_inc_ref(v_k_393_);
v_k_171_ = v_k_393_;
v___y_172_ = v_a_158_;
v___y_173_ = v_a_159_;
v___y_174_ = v_a_160_;
v___y_175_ = v_a_161_;
v___y_176_ = v_a_162_;
goto v___jp_170_;
}
else
{
lean_object* v_cidx_435_; lean_object* v_cidx_436_; uint8_t v___x_437_; 
lean_inc_ref(v_k_393_);
lean_dec_ref_known(v_c_157_, 2);
v_cidx_435_ = lean_ctor_get(v_info_155_, 1);
v_cidx_436_ = lean_ctor_get(v_i_400_, 1);
v___x_437_ = lean_nat_dec_eq(v_cidx_435_, v_cidx_436_);
if (v___x_437_ == 0)
{
uint8_t v___x_438_; 
v___x_438_ = lean_unbox(v_a_411_);
v___y_413_ = v___x_438_;
goto v___jp_412_;
}
else
{
uint8_t v___x_439_; 
v___x_439_ = 0;
v___y_413_ = v___x_439_;
goto v___jp_412_;
}
}
v___jp_412_:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(v___x_414_, 0, v_w_156_);
lean_ctor_set(v___x_414_, 1, v_i_400_);
lean_ctor_set(v___x_414_, 2, v_args_401_);
lean_ctor_set_uint8(v___x_414_, sizeof(void*)*3, v___y_413_);
v___x_415_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_405_, v___x_409_, v_type_396_, v___x_414_, v_a_160_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_425_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_425_ == 0)
{
v___x_418_ = v___x_415_;
v_isShared_419_ = v_isSharedCheck_425_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_415_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_425_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v_a_416_);
lean_ctor_set(v___x_420_, 1, v_k_393_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v_a_411_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_421_);
v___x_423_ = v___x_418_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_dec(v_a_411_);
lean_dec_ref(v_k_393_);
v_a_426_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_415_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_415_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
else
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
lean_dec_ref(v___x_409_);
lean_dec_ref(v_args_401_);
lean_dec_ref(v_i_400_);
lean_dec_ref(v_type_396_);
lean_dec_ref_known(v_c_157_, 2);
lean_dec(v_w_156_);
v_a_440_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___x_410_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_410_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
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
lean_object* v_k_453_; 
lean_dec(v_value_392_);
lean_dec_ref(v_decl_391_);
v_k_453_ = lean_ctor_get(v_c_157_, 1);
lean_inc_ref(v_k_453_);
v_k_171_ = v_k_453_;
v___y_172_ = v_a_158_;
v___y_173_ = v_a_159_;
v___y_174_ = v_a_160_;
v___y_175_ = v_a_161_;
v___y_176_ = v_a_162_;
goto v___jp_170_;
}
}
case 2:
{
lean_object* v_decl_454_; lean_object* v_k_455_; lean_object* v_params_456_; lean_object* v_type_457_; lean_object* v_value_458_; uint8_t v___x_459_; lean_object* v___x_460_; 
v_decl_454_ = lean_ctor_get(v_c_157_, 0);
v_k_455_ = lean_ctor_get(v_c_157_, 1);
v_params_456_ = lean_ctor_get(v_decl_454_, 2);
v_type_457_ = lean_ctor_get(v_decl_454_, 3);
v_value_458_ = lean_ctor_get(v_decl_454_, 4);
v___x_459_ = 1;
lean_inc_ref(v_value_458_);
lean_inc(v_w_156_);
v___x_460_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_155_, v_w_156_, v_value_458_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v_snd_462_; uint8_t v___x_463_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_a_461_);
lean_dec_ref_known(v___x_460_, 1);
v_snd_462_ = lean_ctor_get(v_a_461_, 1);
lean_inc(v_snd_462_);
v___x_463_ = lean_unbox(v_snd_462_);
if (v___x_463_ == 0)
{
lean_dec(v_snd_462_);
lean_dec(v_a_461_);
lean_inc_ref(v_k_455_);
v_k_171_ = v_k_455_;
v___y_172_ = v_a_158_;
v___y_173_ = v_a_159_;
v___y_174_ = v_a_160_;
v___y_175_ = v_a_161_;
v___y_176_ = v_a_162_;
goto v___jp_170_;
}
else
{
lean_object* v_fst_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_513_; 
lean_dec(v_w_156_);
v_fst_464_ = lean_ctor_get(v_a_461_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v_a_461_);
if (v_isSharedCheck_513_ == 0)
{
lean_object* v_unused_514_; 
v_unused_514_ = lean_ctor_get(v_a_461_, 1);
lean_dec(v_unused_514_);
v___x_466_ = v_a_461_;
v_isShared_467_ = v_isSharedCheck_513_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_fst_464_);
lean_dec(v_a_461_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_513_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_468_; 
lean_inc_ref(v_params_456_);
lean_inc_ref(v_type_457_);
lean_inc_ref(v_decl_454_);
v___x_468_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_459_, v_decl_454_, v_type_457_, v_params_456_, v_fst_464_, v_a_160_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_504_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_504_ == 0)
{
v___x_471_ = v___x_468_;
v_isShared_472_ = v_isSharedCheck_504_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_504_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___y_474_; size_t v___x_481_; uint8_t v___x_482_; 
v___x_481_ = lean_ptr_addr(v_k_455_);
v___x_482_ = lean_usize_dec_eq(v___x_481_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
lean_inc_ref(v_k_455_);
v_isSharedCheck_489_ = !lean_is_exclusive(v_c_157_);
if (v_isSharedCheck_489_ == 0)
{
lean_object* v_unused_490_; lean_object* v_unused_491_; 
v_unused_490_ = lean_ctor_get(v_c_157_, 1);
lean_dec(v_unused_490_);
v_unused_491_ = lean_ctor_get(v_c_157_, 0);
lean_dec(v_unused_491_);
v___x_484_ = v_c_157_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_dec(v_c_157_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v_a_469_);
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_469_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_k_455_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
v___y_474_ = v___x_487_;
goto v___jp_473_;
}
}
}
else
{
size_t v___x_492_; size_t v___x_493_; uint8_t v___x_494_; 
v___x_492_ = lean_ptr_addr(v_decl_454_);
v___x_493_ = lean_ptr_addr(v_a_469_);
v___x_494_ = lean_usize_dec_eq(v___x_492_, v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_inc_ref(v_k_455_);
v_isSharedCheck_501_ = !lean_is_exclusive(v_c_157_);
if (v_isSharedCheck_501_ == 0)
{
lean_object* v_unused_502_; lean_object* v_unused_503_; 
v_unused_502_ = lean_ctor_get(v_c_157_, 1);
lean_dec(v_unused_502_);
v_unused_503_ = lean_ctor_get(v_c_157_, 0);
lean_dec(v_unused_503_);
v___x_496_ = v_c_157_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_dec(v_c_157_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v_a_469_);
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_469_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_k_455_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
v___y_474_ = v___x_499_;
goto v___jp_473_;
}
}
}
else
{
lean_dec(v_a_469_);
v___y_474_ = v_c_157_;
goto v___jp_473_;
}
}
v___jp_473_:
{
lean_object* v___x_476_; 
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___y_474_);
v___x_476_ = v___x_466_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___y_474_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_snd_462_);
v___x_476_ = v_reuseFailAlloc_480_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_478_; 
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_476_);
v___x_478_ = v___x_471_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_476_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_del_object(v___x_466_);
lean_dec(v_snd_462_);
lean_dec_ref_known(v_c_157_, 2);
v_a_505_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_468_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_468_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_c_157_, 2);
lean_dec(v_w_156_);
return v___x_460_;
}
}
case 3:
{
uint8_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec(v_w_156_);
v___x_515_ = 0;
v___x_516_ = lean_box(v___x_515_);
v___x_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_517_, 0, v_c_157_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
case 4:
{
lean_object* v_cases_519_; lean_object* v_typeName_520_; lean_object* v_resultType_521_; lean_object* v_discr_522_; lean_object* v_alts_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_575_; 
v_cases_519_ = lean_ctor_get(v_c_157_, 0);
lean_inc_ref(v_cases_519_);
v_typeName_520_ = lean_ctor_get(v_cases_519_, 0);
v_resultType_521_ = lean_ctor_get(v_cases_519_, 1);
v_discr_522_ = lean_ctor_get(v_cases_519_, 2);
v_alts_523_ = lean_ctor_get(v_cases_519_, 3);
v_isSharedCheck_575_ = !lean_is_exclusive(v_cases_519_);
if (v_isSharedCheck_575_ == 0)
{
v___x_525_ = v_cases_519_;
v_isShared_526_ = v_isSharedCheck_575_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_alts_523_);
lean_inc(v_discr_522_);
lean_inc(v_resultType_521_);
lean_inc(v_typeName_520_);
lean_dec(v_cases_519_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_575_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
size_t v_sz_527_; size_t v___x_528_; lean_object* v___x_529_; 
v_sz_527_ = lean_array_size(v_alts_523_);
v___x_528_ = ((size_t)0ULL);
lean_inc_ref(v_alts_523_);
v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(v_info_155_, v_w_156_, v_sz_527_, v___x_528_, v_alts_523_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_566_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_566_ == 0)
{
v___x_532_ = v___x_529_;
v_isShared_533_ = v_isSharedCheck_566_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_566_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___y_535_; uint8_t v___y_536_; lean_object* v___x_542_; lean_object* v_fst_543_; lean_object* v_snd_544_; lean_object* v___y_546_; size_t v___x_552_; size_t v___x_553_; uint8_t v___x_554_; 
v___x_542_ = l_Array_unzip___redArg(v_a_530_);
lean_dec(v_a_530_);
v_fst_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_fst_543_);
v_snd_544_ = lean_ctor_get(v___x_542_, 1);
lean_inc(v_snd_544_);
lean_dec_ref(v___x_542_);
v___x_552_ = lean_ptr_addr(v_alts_523_);
lean_dec_ref(v_alts_523_);
v___x_553_ = lean_ptr_addr(v_fst_543_);
v___x_554_ = lean_usize_dec_eq(v___x_552_, v___x_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_564_; 
v_isSharedCheck_564_ = !lean_is_exclusive(v_c_157_);
if (v_isSharedCheck_564_ == 0)
{
lean_object* v_unused_565_; 
v_unused_565_ = lean_ctor_get(v_c_157_, 0);
lean_dec(v_unused_565_);
v___x_556_ = v_c_157_;
v_isShared_557_ = v_isSharedCheck_564_;
goto v_resetjp_555_;
}
else
{
lean_dec(v_c_157_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_564_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 3, v_fst_543_);
v___x_559_ = v___x_525_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_typeName_520_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_resultType_521_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v_discr_522_);
lean_ctor_set(v_reuseFailAlloc_563_, 3, v_fst_543_);
v___x_559_ = v_reuseFailAlloc_563_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_561_; 
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_559_);
v___x_561_ = v___x_556_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
v___y_546_ = v___x_561_;
goto v___jp_545_;
}
}
}
}
else
{
lean_dec(v_fst_543_);
lean_del_object(v___x_525_);
lean_dec(v_discr_522_);
lean_dec_ref(v_resultType_521_);
lean_dec(v_typeName_520_);
v___y_546_ = v_c_157_;
goto v___jp_545_;
}
v___jp_534_:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_537_ = lean_box(v___y_536_);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v___y_535_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_538_);
v___x_540_ = v___x_532_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
v___jp_545_:
{
lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = lean_array_get_size(v_snd_544_);
v___x_549_ = lean_nat_dec_lt(v___x_547_, v___x_548_);
if (v___x_549_ == 0)
{
lean_dec(v_snd_544_);
v___y_535_ = v___y_546_;
v___y_536_ = v___x_549_;
goto v___jp_534_;
}
else
{
if (v___x_549_ == 0)
{
lean_dec(v_snd_544_);
v___y_535_ = v___y_546_;
v___y_536_ = v___x_549_;
goto v___jp_534_;
}
else
{
size_t v___x_550_; uint8_t v___x_551_; 
v___x_550_ = lean_usize_of_nat(v___x_548_);
v___x_551_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(v_snd_544_, v___x_528_, v___x_550_);
lean_dec(v_snd_544_);
v___y_535_ = v___y_546_;
v___y_536_ = v___x_551_;
goto v___jp_534_;
}
}
}
}
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_del_object(v___x_525_);
lean_dec_ref(v_alts_523_);
lean_dec(v_discr_522_);
lean_dec_ref(v_resultType_521_);
lean_dec(v_typeName_520_);
lean_dec_ref_known(v_c_157_, 1);
v_a_567_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_529_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_529_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
case 5:
{
uint8_t v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v_w_156_);
v___x_576_ = 0;
v___x_577_ = lean_box(v___x_576_);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v_c_157_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
case 6:
{
uint8_t v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec(v_w_156_);
v___x_580_ = 0;
v___x_581_ = lean_box(v___x_580_);
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v_c_157_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
return v___x_583_;
}
case 8:
{
lean_object* v_k_584_; 
v_k_584_ = lean_ctor_get(v_c_157_, 3);
lean_inc_ref(v_k_584_);
v_k_171_ = v_k_584_;
v___y_172_ = v_a_158_;
v___y_173_ = v_a_159_;
v___y_174_ = v_a_160_;
v___y_175_ = v_a_161_;
v___y_176_ = v_a_162_;
goto v___jp_170_;
}
case 9:
{
lean_object* v_k_585_; 
v_k_585_ = lean_ctor_get(v_c_157_, 5);
lean_inc_ref(v_k_585_);
v_k_171_ = v_k_585_;
v___y_172_ = v_a_158_;
v___y_173_ = v_a_159_;
v___y_174_ = v_a_160_;
v___y_175_ = v_a_161_;
v___y_176_ = v_a_162_;
goto v___jp_170_;
}
default: 
{
lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec_ref(v_c_157_);
lean_dec(v_w_156_);
v___x_586_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6);
v___x_587_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(v___x_586_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
return v___x_587_;
}
}
v___jp_164_:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = lean_box(v___y_165_);
v___x_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_168_, 0, v___y_166_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
return v___x_169_;
}
v___jp_170_:
{
lean_object* v___x_177_; 
v___x_177_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_155_, v_w_156_, v_k_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_a_178_);
lean_dec_ref_known(v___x_177_, 1);
switch(lean_obj_tag(v_c_157_))
{
case 0:
{
lean_object* v_fst_179_; lean_object* v_snd_180_; lean_object* v_decl_181_; lean_object* v_k_182_; size_t v___x_183_; size_t v___x_184_; uint8_t v___x_185_; 
v_fst_179_ = lean_ctor_get(v_a_178_, 0);
lean_inc(v_fst_179_);
v_snd_180_ = lean_ctor_get(v_a_178_, 1);
lean_inc(v_snd_180_);
lean_dec(v_a_178_);
v_decl_181_ = lean_ctor_get(v_c_157_, 0);
v_k_182_ = lean_ctor_get(v_c_157_, 1);
v___x_183_ = lean_ptr_addr(v_k_182_);
v___x_184_ = lean_ptr_addr(v_fst_179_);
v___x_185_ = lean_usize_dec_eq(v___x_183_, v___x_184_);
if (v___x_185_ == 0)
{
lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_193_; 
lean_inc_ref(v_decl_181_);
v_isSharedCheck_193_ = !lean_is_exclusive(v_c_157_);
if (v_isSharedCheck_193_ == 0)
{
lean_object* v_unused_194_; lean_object* v_unused_195_; 
v_unused_194_ = lean_ctor_get(v_c_157_, 1);
lean_dec(v_unused_194_);
v_unused_195_ = lean_ctor_get(v_c_157_, 0);
lean_dec(v_unused_195_);
v___x_187_ = v_c_157_;
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
else
{
lean_dec(v_c_157_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 1, v_fst_179_);
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_decl_181_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_fst_179_);
v___x_190_ = v_reuseFailAlloc_192_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
uint8_t v___x_191_; 
v___x_191_ = lean_unbox(v_snd_180_);
lean_dec(v_snd_180_);
v___y_165_ = v___x_191_;
v___y_166_ = v___x_190_;
goto v___jp_164_;
}
}
}
else
{
uint8_t v___x_196_; 
lean_dec(v_fst_179_);
v___x_196_ = lean_unbox(v_snd_180_);
lean_dec(v_snd_180_);
v___y_165_ = v___x_196_;
v___y_166_ = v_c_157_;
goto v___jp_164_;
}
}
case 1:
{
lean_object* v_fst_197_; lean_object* v_snd_198_; lean_object* v_decl_199_; lean_object* v_k_200_; size_t v___x_201_; size_t v___x_202_; uint8_t v___x_203_; 
v_fst_197_ = lean_ctor_get(v_a_178_, 0);
lean_inc(v_fst_197_);
v_snd_198_ = lean_ctor_get(v_a_178_, 1);
lean_inc(v_snd_198_);
lean_dec(v_a_178_);
v_decl_199_ = lean_ctor_get(v_c_157_, 0);
v_k_200_ = lean_ctor_get(v_c_157_, 1);
v___x_201_ = lean_ptr_addr(v_k_200_);
v___x_202_ = lean_ptr_addr(v_fst_197_);
v___x_203_ = lean_usize_dec_eq(v___x_201_, v___x_202_);
if (v___x_203_ == 0)
{
lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_211_; 
lean_inc_ref(v_decl_199_);
v_isSharedCheck_211_ = !lean_is_exclusive(v_c_157_);
if (v_isSharedCheck_211_ == 0)
{
lean_object* v_unused_212_; lean_object* v_unused_213_; 
v_unused_212_ = lean_ctor_get(v_c_157_, 1);
lean_dec(v_unused_212_);
v_unused_213_ = lean_ctor_get(v_c_157_, 0);
lean_dec(v_unused_213_);
v___x_205_ = v_c_157_;
v_isShared_206_ = v_isSharedCheck_211_;
goto v_resetjp_204_;
}
else
{
lean_dec(v_c_157_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_211_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 1, v_fst_197_);
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_decl_199_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v_fst_197_);
v___x_208_ = v_reuseFailAlloc_210_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
uint8_t v___x_209_; 
v___x_209_ = lean_unbox(v_snd_198_);
lean_dec(v_snd_198_);
v___y_165_ = v___x_209_;
v___y_166_ = v___x_208_;
goto v___jp_164_;
}
}
}
else
{
uint8_t v___x_214_; 
lean_dec(v_fst_197_);
v___x_214_ = lean_unbox(v_snd_198_);
lean_dec(v_snd_198_);
v___y_165_ = v___x_214_;
v___y_166_ = v_c_157_;
goto v___jp_164_;
}
}
case 2:
{
lean_object* v_fst_215_; lean_object* v_snd_216_; lean_object* v_decl_217_; lean_object* v_k_218_; size_t v___x_219_; size_t v___x_220_; uint8_t v___x_221_; 
v_fst_215_ = lean_ctor_get(v_a_178_, 0);
lean_inc(v_fst_215_);
v_snd_216_ = lean_ctor_get(v_a_178_, 1);
lean_inc(v_snd_216_);
lean_dec(v_a_178_);
v_decl_217_ = lean_ctor_get(v_c_157_, 0);
v_k_218_ = lean_ctor_get(v_c_157_, 1);
v___x_219_ = lean_ptr_addr(v_k_218_);
v___x_220_ = lean_ptr_addr(v_fst_215_);
v___x_221_ = lean_usize_dec_eq(v___x_219_, v___x_220_);
if (v___x_221_ == 0)
{
lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_229_; 
lean_inc_ref(v_decl_217_);
v_isSharedCheck_229_ = !lean_is_exclusive(v_c_157_);
if (v_isSharedCheck_229_ == 0)
{
lean_object* v_unused_230_; lean_object* v_unused_231_; 
v_unused_230_ = lean_ctor_get(v_c_157_, 1);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_c_157_, 0);
lean_dec(v_unused_231_);
v___x_223_ = v_c_157_;
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
else
{
lean_dec(v_c_157_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v_fst_215_);
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_decl_217_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_fst_215_);
v___x_226_ = v_reuseFailAlloc_228_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
uint8_t v___x_227_; 
v___x_227_ = lean_unbox(v_snd_216_);
lean_dec(v_snd_216_);
v___y_165_ = v___x_227_;
v___y_166_ = v___x_226_;
goto v___jp_164_;
}
}
}
else
{
uint8_t v___x_232_; 
lean_dec(v_fst_215_);
v___x_232_ = lean_unbox(v_snd_216_);
lean_dec(v_snd_216_);
v___y_165_ = v___x_232_;
v___y_166_ = v_c_157_;
goto v___jp_164_;
}
}
case 7:
{
lean_object* v_fst_233_; lean_object* v_snd_234_; lean_object* v_fvarId_235_; lean_object* v_i_236_; lean_object* v_y_237_; lean_object* v_k_238_; size_t v___x_239_; size_t v___x_240_; uint8_t v___x_241_; 
v_fst_233_ = lean_ctor_get(v_a_178_, 0);
lean_inc(v_fst_233_);
v_snd_234_ = lean_ctor_get(v_a_178_, 1);
lean_inc(v_snd_234_);
lean_dec(v_a_178_);
v_fvarId_235_ = lean_ctor_get(v_c_157_, 0);
v_i_236_ = lean_ctor_get(v_c_157_, 1);
v_y_237_ = lean_ctor_get(v_c_157_, 2);
v_k_238_ = lean_ctor_get(v_c_157_, 3);
v___x_239_ = lean_ptr_addr(v_k_238_);
v___x_240_ = lean_ptr_addr(v_fst_233_);
v___x_241_ = lean_usize_dec_eq(v___x_239_, v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_249_; 
lean_inc(v_y_237_);
lean_inc(v_i_236_);
lean_inc(v_fvarId_235_);
v_isSharedCheck_249_ = !lean_is_exclusive(v_c_157_);
if (v_isSharedCheck_249_ == 0)
{
lean_object* v_unused_250_; lean_object* v_unused_251_; lean_object* v_unused_252_; lean_object* v_unused_253_; 
v_unused_250_ = lean_ctor_get(v_c_157_, 3);
lean_dec(v_unused_250_);
v_unused_251_ = lean_ctor_get(v_c_157_, 2);
lean_dec(v_unused_251_);
v_unused_252_ = lean_ctor_get(v_c_157_, 1);
lean_dec(v_unused_252_);
v_unused_253_ = lean_ctor_get(v_c_157_, 0);
lean_dec(v_unused_253_);
v___x_243_ = v_c_157_;
v_isShared_244_ = v_isSharedCheck_249_;
goto v_resetjp_242_;
}
else
{
lean_dec(v_c_157_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_249_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 3, v_fst_233_);
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_fvarId_235_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v_i_236_);
lean_ctor_set(v_reuseFailAlloc_248_, 2, v_y_237_);
lean_ctor_set(v_reuseFailAlloc_248_, 3, v_fst_233_);
v___x_246_ = v_reuseFailAlloc_248_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
uint8_t v___x_247_; 
v___x_247_ = lean_unbox(v_snd_234_);
lean_dec(v_snd_234_);
v___y_165_ = v___x_247_;
v___y_166_ = v___x_246_;
goto v___jp_164_;
}
}
}
else
{
uint8_t v___x_254_; 
lean_dec(v_fst_233_);
v___x_254_ = lean_unbox(v_snd_234_);
lean_dec(v_snd_234_);
v___y_165_ = v___x_254_;
v___y_166_ = v_c_157_;
goto v___jp_164_;
}
}
case 9:
{
lean_object* v_fst_255_; lean_object* v_snd_256_; lean_object* v_fvarId_257_; lean_object* v_i_258_; lean_object* v_offset_259_; lean_object* v_y_260_; lean_object* v_ty_261_; lean_object* v_k_262_; size_t v___x_263_; size_t v___x_264_; uint8_t v___x_265_; 
v_fst_255_ = lean_ctor_get(v_a_178_, 0);
lean_inc(v_fst_255_);
v_snd_256_ = lean_ctor_get(v_a_178_, 1);
lean_inc(v_snd_256_);
lean_dec(v_a_178_);
v_fvarId_257_ = lean_ctor_get(v_c_157_, 0);
v_i_258_ = lean_ctor_get(v_c_157_, 1);
v_offset_259_ = lean_ctor_get(v_c_157_, 2);
v_y_260_ = lean_ctor_get(v_c_157_, 3);
v_ty_261_ = lean_ctor_get(v_c_157_, 4);
v_k_262_ = lean_ctor_get(v_c_157_, 5);
v___x_263_ = lean_ptr_addr(v_k_262_);
v___x_264_ = lean_ptr_addr(v_fst_255_);
v___x_265_ = lean_usize_dec_eq(v___x_263_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_273_; 
lean_inc_ref(v_ty_261_);
lean_inc(v_y_260_);
lean_inc(v_offset_259_);
lean_inc(v_i_258_);
lean_inc(v_fvarId_257_);
v_isSharedCheck_273_ = !lean_is_exclusive(v_c_157_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; lean_object* v_unused_275_; lean_object* v_unused_276_; lean_object* v_unused_277_; lean_object* v_unused_278_; lean_object* v_unused_279_; 
v_unused_274_ = lean_ctor_get(v_c_157_, 5);
lean_dec(v_unused_274_);
v_unused_275_ = lean_ctor_get(v_c_157_, 4);
lean_dec(v_unused_275_);
v_unused_276_ = lean_ctor_get(v_c_157_, 3);
lean_dec(v_unused_276_);
v_unused_277_ = lean_ctor_get(v_c_157_, 2);
lean_dec(v_unused_277_);
v_unused_278_ = lean_ctor_get(v_c_157_, 1);
lean_dec(v_unused_278_);
v_unused_279_ = lean_ctor_get(v_c_157_, 0);
lean_dec(v_unused_279_);
v___x_267_ = v_c_157_;
v_isShared_268_ = v_isSharedCheck_273_;
goto v_resetjp_266_;
}
else
{
lean_dec(v_c_157_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_273_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 5, v_fst_255_);
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_fvarId_257_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_i_258_);
lean_ctor_set(v_reuseFailAlloc_272_, 2, v_offset_259_);
lean_ctor_set(v_reuseFailAlloc_272_, 3, v_y_260_);
lean_ctor_set(v_reuseFailAlloc_272_, 4, v_ty_261_);
lean_ctor_set(v_reuseFailAlloc_272_, 5, v_fst_255_);
v___x_270_ = v_reuseFailAlloc_272_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
uint8_t v___x_271_; 
v___x_271_ = lean_unbox(v_snd_256_);
lean_dec(v_snd_256_);
v___y_165_ = v___x_271_;
v___y_166_ = v___x_270_;
goto v___jp_164_;
}
}
}
else
{
uint8_t v___x_280_; 
lean_dec(v_fst_255_);
v___x_280_ = lean_unbox(v_snd_256_);
lean_dec(v_snd_256_);
v___y_165_ = v___x_280_;
v___y_166_ = v_c_157_;
goto v___jp_164_;
}
}
case 8:
{
lean_object* v_fst_281_; lean_object* v_snd_282_; lean_object* v_fvarId_283_; lean_object* v_i_284_; lean_object* v_y_285_; lean_object* v_k_286_; size_t v___x_287_; size_t v___x_288_; uint8_t v___x_289_; 
v_fst_281_ = lean_ctor_get(v_a_178_, 0);
lean_inc(v_fst_281_);
v_snd_282_ = lean_ctor_get(v_a_178_, 1);
lean_inc(v_snd_282_);
lean_dec(v_a_178_);
v_fvarId_283_ = lean_ctor_get(v_c_157_, 0);
v_i_284_ = lean_ctor_get(v_c_157_, 1);
v_y_285_ = lean_ctor_get(v_c_157_, 2);
v_k_286_ = lean_ctor_get(v_c_157_, 3);
v___x_287_ = lean_ptr_addr(v_k_286_);
v___x_288_ = lean_ptr_addr(v_fst_281_);
v___x_289_ = lean_usize_dec_eq(v___x_287_, v___x_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_297_; 
lean_inc(v_y_285_);
lean_inc(v_i_284_);
lean_inc(v_fvarId_283_);
v_isSharedCheck_297_ = !lean_is_exclusive(v_c_157_);
if (v_isSharedCheck_297_ == 0)
{
lean_object* v_unused_298_; lean_object* v_unused_299_; lean_object* v_unused_300_; lean_object* v_unused_301_; 
v_unused_298_ = lean_ctor_get(v_c_157_, 3);
lean_dec(v_unused_298_);
v_unused_299_ = lean_ctor_get(v_c_157_, 2);
lean_dec(v_unused_299_);
v_unused_300_ = lean_ctor_get(v_c_157_, 1);
lean_dec(v_unused_300_);
v_unused_301_ = lean_ctor_get(v_c_157_, 0);
lean_dec(v_unused_301_);
v___x_291_ = v_c_157_;
v_isShared_292_ = v_isSharedCheck_297_;
goto v_resetjp_290_;
}
else
{
lean_dec(v_c_157_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_297_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 3, v_fst_281_);
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_fvarId_283_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_i_284_);
lean_ctor_set(v_reuseFailAlloc_296_, 2, v_y_285_);
lean_ctor_set(v_reuseFailAlloc_296_, 3, v_fst_281_);
v___x_294_ = v_reuseFailAlloc_296_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
uint8_t v___x_295_; 
v___x_295_ = lean_unbox(v_snd_282_);
lean_dec(v_snd_282_);
v___y_165_ = v___x_295_;
v___y_166_ = v___x_294_;
goto v___jp_164_;
}
}
}
else
{
uint8_t v___x_302_; 
lean_dec(v_fst_281_);
v___x_302_ = lean_unbox(v_snd_282_);
lean_dec(v_snd_282_);
v___y_165_ = v___x_302_;
v___y_166_ = v_c_157_;
goto v___jp_164_;
}
}
case 10:
{
lean_object* v_fst_303_; lean_object* v_snd_304_; lean_object* v_fvarId_305_; lean_object* v_cidx_306_; lean_object* v_k_307_; size_t v___x_308_; size_t v___x_309_; uint8_t v___x_310_; 
v_fst_303_ = lean_ctor_get(v_a_178_, 0);
lean_inc(v_fst_303_);
v_snd_304_ = lean_ctor_get(v_a_178_, 1);
lean_inc(v_snd_304_);
lean_dec(v_a_178_);
v_fvarId_305_ = lean_ctor_get(v_c_157_, 0);
v_cidx_306_ = lean_ctor_get(v_c_157_, 1);
v_k_307_ = lean_ctor_get(v_c_157_, 2);
v___x_308_ = lean_ptr_addr(v_k_307_);
v___x_309_ = lean_ptr_addr(v_fst_303_);
v___x_310_ = lean_usize_dec_eq(v___x_308_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_318_; 
lean_inc(v_cidx_306_);
lean_inc(v_fvarId_305_);
v_isSharedCheck_318_ = !lean_is_exclusive(v_c_157_);
if (v_isSharedCheck_318_ == 0)
{
lean_object* v_unused_319_; lean_object* v_unused_320_; lean_object* v_unused_321_; 
v_unused_319_ = lean_ctor_get(v_c_157_, 2);
lean_dec(v_unused_319_);
v_unused_320_ = lean_ctor_get(v_c_157_, 1);
lean_dec(v_unused_320_);
v_unused_321_ = lean_ctor_get(v_c_157_, 0);
lean_dec(v_unused_321_);
v___x_312_ = v_c_157_;
v_isShared_313_ = v_isSharedCheck_318_;
goto v_resetjp_311_;
}
else
{
lean_dec(v_c_157_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_318_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 2, v_fst_303_);
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_fvarId_305_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_cidx_306_);
lean_ctor_set(v_reuseFailAlloc_317_, 2, v_fst_303_);
v___x_315_ = v_reuseFailAlloc_317_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
uint8_t v___x_316_; 
v___x_316_ = lean_unbox(v_snd_304_);
lean_dec(v_snd_304_);
v___y_165_ = v___x_316_;
v___y_166_ = v___x_315_;
goto v___jp_164_;
}
}
}
else
{
uint8_t v___x_322_; 
lean_dec(v_fst_303_);
v___x_322_ = lean_unbox(v_snd_304_);
lean_dec(v_snd_304_);
v___y_165_ = v___x_322_;
v___y_166_ = v_c_157_;
goto v___jp_164_;
}
}
case 11:
{
lean_object* v_fst_323_; lean_object* v_snd_324_; lean_object* v_fvarId_325_; lean_object* v_n_326_; uint8_t v_check_327_; uint8_t v_persistent_328_; lean_object* v_k_329_; size_t v___x_330_; size_t v___x_331_; uint8_t v___x_332_; 
v_fst_323_ = lean_ctor_get(v_a_178_, 0);
lean_inc(v_fst_323_);
v_snd_324_ = lean_ctor_get(v_a_178_, 1);
lean_inc(v_snd_324_);
lean_dec(v_a_178_);
v_fvarId_325_ = lean_ctor_get(v_c_157_, 0);
v_n_326_ = lean_ctor_get(v_c_157_, 1);
v_check_327_ = lean_ctor_get_uint8(v_c_157_, sizeof(void*)*3);
v_persistent_328_ = lean_ctor_get_uint8(v_c_157_, sizeof(void*)*3 + 1);
v_k_329_ = lean_ctor_get(v_c_157_, 2);
v___x_330_ = lean_ptr_addr(v_k_329_);
v___x_331_ = lean_ptr_addr(v_fst_323_);
v___x_332_ = lean_usize_dec_eq(v___x_330_, v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_340_; 
lean_inc(v_n_326_);
lean_inc(v_fvarId_325_);
v_isSharedCheck_340_ = !lean_is_exclusive(v_c_157_);
if (v_isSharedCheck_340_ == 0)
{
lean_object* v_unused_341_; lean_object* v_unused_342_; lean_object* v_unused_343_; 
v_unused_341_ = lean_ctor_get(v_c_157_, 2);
lean_dec(v_unused_341_);
v_unused_342_ = lean_ctor_get(v_c_157_, 1);
lean_dec(v_unused_342_);
v_unused_343_ = lean_ctor_get(v_c_157_, 0);
lean_dec(v_unused_343_);
v___x_334_ = v_c_157_;
v_isShared_335_ = v_isSharedCheck_340_;
goto v_resetjp_333_;
}
else
{
lean_dec(v_c_157_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_340_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 2, v_fst_323_);
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_fvarId_325_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_n_326_);
lean_ctor_set(v_reuseFailAlloc_339_, 2, v_fst_323_);
lean_ctor_set_uint8(v_reuseFailAlloc_339_, sizeof(void*)*3, v_check_327_);
lean_ctor_set_uint8(v_reuseFailAlloc_339_, sizeof(void*)*3 + 1, v_persistent_328_);
v___x_337_ = v_reuseFailAlloc_339_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
uint8_t v___x_338_; 
v___x_338_ = lean_unbox(v_snd_324_);
lean_dec(v_snd_324_);
v___y_165_ = v___x_338_;
v___y_166_ = v___x_337_;
goto v___jp_164_;
}
}
}
else
{
uint8_t v___x_344_; 
lean_dec(v_fst_323_);
v___x_344_ = lean_unbox(v_snd_324_);
lean_dec(v_snd_324_);
v___y_165_ = v___x_344_;
v___y_166_ = v_c_157_;
goto v___jp_164_;
}
}
case 12:
{
lean_object* v_fst_345_; lean_object* v_snd_346_; lean_object* v_fvarId_347_; lean_object* v_n_348_; uint8_t v_check_349_; uint8_t v_persistent_350_; lean_object* v_objs_x3f_351_; lean_object* v_k_352_; size_t v___x_353_; size_t v___x_354_; uint8_t v___x_355_; 
v_fst_345_ = lean_ctor_get(v_a_178_, 0);
lean_inc(v_fst_345_);
v_snd_346_ = lean_ctor_get(v_a_178_, 1);
lean_inc(v_snd_346_);
lean_dec(v_a_178_);
v_fvarId_347_ = lean_ctor_get(v_c_157_, 0);
v_n_348_ = lean_ctor_get(v_c_157_, 1);
v_check_349_ = lean_ctor_get_uint8(v_c_157_, sizeof(void*)*4);
v_persistent_350_ = lean_ctor_get_uint8(v_c_157_, sizeof(void*)*4 + 1);
v_objs_x3f_351_ = lean_ctor_get(v_c_157_, 2);
v_k_352_ = lean_ctor_get(v_c_157_, 3);
v___x_353_ = lean_ptr_addr(v_k_352_);
v___x_354_ = lean_ptr_addr(v_fst_345_);
v___x_355_ = lean_usize_dec_eq(v___x_353_, v___x_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_363_; 
lean_inc(v_objs_x3f_351_);
lean_inc(v_n_348_);
lean_inc(v_fvarId_347_);
v_isSharedCheck_363_ = !lean_is_exclusive(v_c_157_);
if (v_isSharedCheck_363_ == 0)
{
lean_object* v_unused_364_; lean_object* v_unused_365_; lean_object* v_unused_366_; lean_object* v_unused_367_; 
v_unused_364_ = lean_ctor_get(v_c_157_, 3);
lean_dec(v_unused_364_);
v_unused_365_ = lean_ctor_get(v_c_157_, 2);
lean_dec(v_unused_365_);
v_unused_366_ = lean_ctor_get(v_c_157_, 1);
lean_dec(v_unused_366_);
v_unused_367_ = lean_ctor_get(v_c_157_, 0);
lean_dec(v_unused_367_);
v___x_357_ = v_c_157_;
v_isShared_358_ = v_isSharedCheck_363_;
goto v_resetjp_356_;
}
else
{
lean_dec(v_c_157_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_363_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 3, v_fst_345_);
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_fvarId_347_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_n_348_);
lean_ctor_set(v_reuseFailAlloc_362_, 2, v_objs_x3f_351_);
lean_ctor_set(v_reuseFailAlloc_362_, 3, v_fst_345_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, sizeof(void*)*4, v_check_349_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, sizeof(void*)*4 + 1, v_persistent_350_);
v___x_360_ = v_reuseFailAlloc_362_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
uint8_t v___x_361_; 
v___x_361_ = lean_unbox(v_snd_346_);
lean_dec(v_snd_346_);
v___y_165_ = v___x_361_;
v___y_166_ = v___x_360_;
goto v___jp_164_;
}
}
}
else
{
uint8_t v___x_368_; 
lean_dec(v_fst_345_);
v___x_368_ = lean_unbox(v_snd_346_);
lean_dec(v_snd_346_);
v___y_165_ = v___x_368_;
v___y_166_ = v_c_157_;
goto v___jp_164_;
}
}
case 13:
{
lean_object* v_fst_369_; lean_object* v_snd_370_; lean_object* v_fvarId_371_; lean_object* v_k_372_; size_t v___x_373_; size_t v___x_374_; uint8_t v___x_375_; 
v_fst_369_ = lean_ctor_get(v_a_178_, 0);
lean_inc(v_fst_369_);
v_snd_370_ = lean_ctor_get(v_a_178_, 1);
lean_inc(v_snd_370_);
lean_dec(v_a_178_);
v_fvarId_371_ = lean_ctor_get(v_c_157_, 0);
v_k_372_ = lean_ctor_get(v_c_157_, 1);
v___x_373_ = lean_ptr_addr(v_k_372_);
v___x_374_ = lean_ptr_addr(v_fst_369_);
v___x_375_ = lean_usize_dec_eq(v___x_373_, v___x_374_);
if (v___x_375_ == 0)
{
lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_383_; 
lean_inc(v_fvarId_371_);
v_isSharedCheck_383_ = !lean_is_exclusive(v_c_157_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; lean_object* v_unused_385_; 
v_unused_384_ = lean_ctor_get(v_c_157_, 1);
lean_dec(v_unused_384_);
v_unused_385_ = lean_ctor_get(v_c_157_, 0);
lean_dec(v_unused_385_);
v___x_377_ = v_c_157_;
v_isShared_378_ = v_isSharedCheck_383_;
goto v_resetjp_376_;
}
else
{
lean_dec(v_c_157_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_383_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 1, v_fst_369_);
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_fvarId_371_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_fst_369_);
v___x_380_ = v_reuseFailAlloc_382_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
uint8_t v___x_381_; 
v___x_381_ = lean_unbox(v_snd_370_);
lean_dec(v_snd_370_);
v___y_165_ = v___x_381_;
v___y_166_ = v___x_380_;
goto v___jp_164_;
}
}
}
else
{
uint8_t v___x_386_; 
lean_dec(v_fst_369_);
v___x_386_ = lean_unbox(v_snd_370_);
lean_dec(v_snd_370_);
v___y_165_ = v___x_386_;
v___y_166_ = v_c_157_;
goto v___jp_164_;
}
}
default: 
{
lean_object* v_snd_387_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
lean_dec_ref(v_c_157_);
v_snd_387_ = lean_ctor_get(v_a_178_, 1);
lean_inc(v_snd_387_);
lean_dec(v_a_178_);
v___x_388_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3);
v___x_389_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0(v___x_388_);
v___x_390_ = lean_unbox(v_snd_387_);
lean_dec(v_snd_387_);
v___y_165_ = v___x_390_;
v___y_166_ = v___x_389_;
goto v___jp_164_;
}
}
}
else
{
lean_dec_ref(v_c_157_);
return v___x_177_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_155_ = stack[0].m_obj;
lean_object* v_w_156_ = stack[1].m_obj;
lean_object* v_c_157_ = stack[2].m_obj;
lean_object* v_a_158_ = stack[3].m_obj;
lean_object* v_a_159_ = stack[4].m_obj;
lean_object* v_a_160_ = stack[5].m_obj;
lean_object* v_a_161_ = stack[6].m_obj;
lean_object* v_a_162_ = stack[7].m_obj;
lean_object* v_res_588_;
v_res_588_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_155_, v_w_156_, v_c_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
stack->m_obj
 = v_res_588_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(lean_object* v_info_589_, lean_object* v_w_590_, size_t v_sz_591_, size_t v_i_592_, lean_object* v_bs_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
uint8_t v___x_600_; 
v___x_600_ = lean_usize_dec_lt(v_i_592_, v_sz_591_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; 
lean_dec(v_w_590_);
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v_bs_593_);
return v___x_601_;
}
else
{
lean_object* v_v_602_; lean_object* v___x_603_; lean_object* v_bs_x27_604_; lean_object* v___y_606_; 
v_v_602_ = lean_array_uget(v_bs_593_, v_i_592_);
v___x_603_ = lean_unsigned_to_nat(0u);
v_bs_x27_604_ = lean_array_uset(v_bs_593_, v_i_592_, v___x_603_);
switch(lean_obj_tag(v_v_602_))
{
case 0:
{
lean_object* v_code_631_; 
v_code_631_ = lean_ctor_get(v_v_602_, 2);
lean_inc_ref(v_code_631_);
v___y_606_ = v_code_631_;
goto v___jp_605_;
}
case 1:
{
lean_object* v_code_632_; 
v_code_632_ = lean_ctor_get(v_v_602_, 1);
lean_inc_ref(v_code_632_);
v___y_606_ = v_code_632_;
goto v___jp_605_;
}
default: 
{
lean_object* v_code_633_; 
v_code_633_ = lean_ctor_get(v_v_602_, 0);
lean_inc_ref(v_code_633_);
v___y_606_ = v_code_633_;
goto v___jp_605_;
}
}
v___jp_605_:
{
lean_object* v___x_607_; 
lean_inc(v_w_590_);
v___x_607_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_589_, v_w_590_, v___y_606_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v_fst_609_; lean_object* v_snd_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_622_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref_known(v___x_607_, 1);
v_fst_609_ = lean_ctor_get(v_a_608_, 0);
v_snd_610_ = lean_ctor_get(v_a_608_, 1);
v_isSharedCheck_622_ = !lean_is_exclusive(v_a_608_);
if (v_isSharedCheck_622_ == 0)
{
v___x_612_ = v_a_608_;
v_isShared_613_ = v_isSharedCheck_622_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_snd_610_);
lean_inc(v_fst_609_);
lean_dec(v_a_608_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_622_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_614_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_602_, v_fst_609_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_614_);
v___x_616_ = v___x_612_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_614_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_snd_610_);
v___x_616_ = v_reuseFailAlloc_621_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
size_t v___x_617_; size_t v___x_618_; lean_object* v___x_619_; 
v___x_617_ = ((size_t)1ULL);
v___x_618_ = lean_usize_add(v_i_592_, v___x_617_);
v___x_619_ = lean_array_uset(v_bs_x27_604_, v_i_592_, v___x_616_);
v_i_592_ = v___x_618_;
v_bs_593_ = v___x_619_;
goto _start;
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref(v_bs_x27_604_);
lean_dec(v_v_602_);
lean_dec(v_w_590_);
v_a_623_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_607_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_607_);
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
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_589_ = stack[0].m_obj;
lean_object* v_w_590_ = stack[1].m_obj;
size_t v_sz_591_ = stack[2].m_num;
size_t v_i_592_ = stack[3].m_num;
lean_object* v_bs_593_ = stack[4].m_obj;
lean_object* v___y_594_ = stack[5].m_obj;
lean_object* v___y_595_ = stack[6].m_obj;
lean_object* v___y_596_ = stack[7].m_obj;
lean_object* v___y_597_ = stack[8].m_obj;
lean_object* v___y_598_ = stack[9].m_obj;
lean_object* v_res_634_;
v_res_634_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(v_info_589_, v_w_590_, v_sz_591_, v_i_592_, v_bs_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
stack->m_obj
 = v_res_634_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1___boxed(lean_object* v_info_635_, lean_object* v_w_636_, lean_object* v_sz_637_, lean_object* v_i_638_, lean_object* v_bs_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
size_t v_sz_boxed_646_; size_t v_i_boxed_647_; lean_object* v_res_648_; 
v_sz_boxed_646_ = lean_unbox_usize(v_sz_637_);
lean_dec(v_sz_637_);
v_i_boxed_647_ = lean_unbox_usize(v_i_638_);
lean_dec(v_i_638_);
v_res_648_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(v_info_635_, v_w_636_, v_sz_boxed_646_, v_i_boxed_647_, v_bs_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec_ref(v_info_635_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___boxed(lean_object* v_info_649_, lean_object* v_w_650_, lean_object* v_c_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_649_, v_w_650_, v_c_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
lean_dec(v_a_654_);
lean_dec_ref(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec_ref(v_info_649_);
return v_res_658_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(lean_object* v___y_659_){
_start:
{
lean_object* v___x_661_; lean_object* v_ngen_662_; lean_object* v_namePrefix_663_; lean_object* v_idx_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_694_; 
v___x_661_ = lean_st_ref_get(v___y_659_);
v_ngen_662_ = lean_ctor_get(v___x_661_, 2);
lean_inc_ref(v_ngen_662_);
lean_dec(v___x_661_);
v_namePrefix_663_ = lean_ctor_get(v_ngen_662_, 0);
v_idx_664_ = lean_ctor_get(v_ngen_662_, 1);
v_isSharedCheck_694_ = !lean_is_exclusive(v_ngen_662_);
if (v_isSharedCheck_694_ == 0)
{
v___x_666_ = v_ngen_662_;
v_isShared_667_ = v_isSharedCheck_694_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_idx_664_);
lean_inc(v_namePrefix_663_);
lean_dec(v_ngen_662_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_694_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v_r_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_672_; 
lean_inc(v_idx_664_);
lean_inc(v_namePrefix_663_);
v_r_668_ = l_Lean_Name_num___override(v_namePrefix_663_, v_idx_664_);
v___x_669_ = lean_unsigned_to_nat(1u);
v___x_670_ = lean_nat_add(v_idx_664_, v___x_669_);
lean_dec(v_idx_664_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v___x_670_);
v___x_672_ = v___x_666_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_namePrefix_663_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v___x_670_);
v___x_672_ = v_reuseFailAlloc_693_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_673_; lean_object* v_env_674_; lean_object* v_nextMacroScope_675_; lean_object* v_auxDeclNGen_676_; lean_object* v_traceState_677_; lean_object* v_cache_678_; lean_object* v_recordedDeps_679_; lean_object* v_messages_680_; lean_object* v_infoState_681_; lean_object* v_snapshotTasks_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_691_; 
v___x_673_ = lean_st_ref_take(v___y_659_);
v_env_674_ = lean_ctor_get(v___x_673_, 0);
v_nextMacroScope_675_ = lean_ctor_get(v___x_673_, 1);
v_auxDeclNGen_676_ = lean_ctor_get(v___x_673_, 3);
v_traceState_677_ = lean_ctor_get(v___x_673_, 4);
v_cache_678_ = lean_ctor_get(v___x_673_, 5);
v_recordedDeps_679_ = lean_ctor_get(v___x_673_, 6);
v_messages_680_ = lean_ctor_get(v___x_673_, 7);
v_infoState_681_ = lean_ctor_get(v___x_673_, 8);
v_snapshotTasks_682_ = lean_ctor_get(v___x_673_, 9);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_691_ == 0)
{
lean_object* v_unused_692_; 
v_unused_692_ = lean_ctor_get(v___x_673_, 2);
lean_dec(v_unused_692_);
v___x_684_ = v___x_673_;
v_isShared_685_ = v_isSharedCheck_691_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_snapshotTasks_682_);
lean_inc(v_infoState_681_);
lean_inc(v_messages_680_);
lean_inc(v_recordedDeps_679_);
lean_inc(v_cache_678_);
lean_inc(v_traceState_677_);
lean_inc(v_auxDeclNGen_676_);
lean_inc(v_nextMacroScope_675_);
lean_inc(v_env_674_);
lean_dec(v___x_673_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_691_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 2, v___x_672_);
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_env_674_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_nextMacroScope_675_);
lean_ctor_set(v_reuseFailAlloc_690_, 2, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_690_, 3, v_auxDeclNGen_676_);
lean_ctor_set(v_reuseFailAlloc_690_, 4, v_traceState_677_);
lean_ctor_set(v_reuseFailAlloc_690_, 5, v_cache_678_);
lean_ctor_set(v_reuseFailAlloc_690_, 6, v_recordedDeps_679_);
lean_ctor_set(v_reuseFailAlloc_690_, 7, v_messages_680_);
lean_ctor_set(v_reuseFailAlloc_690_, 8, v_infoState_681_);
lean_ctor_set(v_reuseFailAlloc_690_, 9, v_snapshotTasks_682_);
v___x_687_ = v_reuseFailAlloc_690_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = lean_st_ref_put(v___y_659_, v___x_687_);
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v_r_668_);
return v___x_689_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_659_ = stack[0].m_obj;
lean_object* v_res_695_;
v_res_695_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(v___y_659_);
stack->m_obj
 = v_res_695_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg___boxed(lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(v___y_696_);
lean_dec(v___y_696_);
return v_res_698_;
}
}
lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v___x_705_; lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
v___x_705_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(v___y_703_);
v_a_706_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_705_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_705_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_699_ = stack[0].m_obj;
lean_object* v___y_700_ = stack[1].m_obj;
lean_object* v___y_701_ = stack[2].m_obj;
lean_object* v___y_702_ = stack[3].m_obj;
lean_object* v___y_703_ = stack[4].m_obj;
lean_object* v_res_714_;
v_res_714_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
stack->m_obj
 = v_res_714_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0___boxed(lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec_ref(v___y_715_);
return v_res_721_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_728_ = lean_box(0);
v___x_729_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__3));
v___x_730_ = l_Lean_Expr_const___override(v___x_729_, v___x_728_);
return v___x_730_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(lean_object* v_x_731_, lean_object* v_info_732_, lean_object* v_c_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_742_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc_n(v_a_741_, 2);
lean_dec_ref_known(v___x_740_, 1);
v___x_742_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_732_, v_a_741_, v_c_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_797_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_797_ == 0)
{
v___x_745_ = v___x_742_;
v_isShared_746_ = v_isSharedCheck_797_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_742_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_797_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v_snd_747_; uint8_t v___x_748_; 
v_snd_747_ = lean_ctor_get(v_a_743_, 1);
v___x_748_ = lean_unbox(v_snd_747_);
if (v___x_748_ == 0)
{
lean_object* v_fst_749_; lean_object* v___x_751_; 
lean_dec(v_a_741_);
lean_dec(v_x_731_);
v_fst_749_ = lean_ctor_get(v_a_743_, 0);
lean_inc(v_fst_749_);
lean_dec(v_a_743_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v_fst_749_);
v___x_751_ = v___x_745_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_fst_749_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
else
{
lean_object* v_fst_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_795_; 
lean_del_object(v___x_745_);
v_fst_753_ = lean_ctor_get(v_a_743_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v_a_743_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; 
v_unused_796_ = lean_ctor_get(v_a_743_, 1);
lean_dec(v_unused_796_);
v___x_755_ = v_a_743_;
v_isShared_756_ = v_isSharedCheck_795_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_fst_753_);
lean_dec(v_a_743_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_795_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__1));
v___x_758_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_757_, v_a_736_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_786_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_786_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_786_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_786_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_size_763_; uint8_t v___x_764_; lean_object* v___x_765_; lean_object* v___x_767_; 
v_size_763_ = lean_ctor_get(v_info_732_, 2);
v___x_764_ = 1;
v___x_765_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4);
lean_inc(v_size_763_);
if (v_isShared_756_ == 0)
{
lean_ctor_set_tag(v___x_755_, 11);
lean_ctor_set(v___x_755_, 1, v_x_731_);
lean_ctor_set(v___x_755_, 0, v_size_763_);
v___x_767_ = v___x_755_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_size_763_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_x_731_);
v___x_767_ = v_reuseFailAlloc_785_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v_lctx_770_; lean_object* v_nextIdx_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_784_; 
v___x_768_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_768_, 0, v_a_741_);
lean_ctor_set(v___x_768_, 1, v_a_759_);
lean_ctor_set(v___x_768_, 2, v___x_765_);
lean_ctor_set(v___x_768_, 3, v___x_767_);
v___x_769_ = lean_st_ref_take(v_a_736_);
v_lctx_770_ = lean_ctor_get(v___x_769_, 0);
v_nextIdx_771_ = lean_ctor_get(v___x_769_, 1);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_784_ == 0)
{
v___x_773_ = v___x_769_;
v_isShared_774_ = v_isSharedCheck_784_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_nextIdx_771_);
lean_inc(v_lctx_770_);
lean_dec(v___x_769_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_784_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_775_; lean_object* v___x_777_; 
lean_inc_ref(v___x_768_);
v___x_775_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_764_, v_lctx_770_, v___x_768_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_775_);
v___x_777_ = v___x_773_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_nextIdx_771_);
v___x_777_ = v_reuseFailAlloc_783_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_778_ = lean_st_ref_put(v_a_736_, v___x_777_);
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_768_);
lean_ctor_set(v___x_779_, 1, v_fst_753_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v___x_779_);
v___x_781_ = v___x_761_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_del_object(v___x_755_);
lean_dec(v_fst_753_);
lean_dec(v_a_741_);
lean_dec(v_x_731_);
v_a_787_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_758_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_758_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec(v_a_741_);
lean_dec(v_x_731_);
v_a_798_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_742_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_742_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec_ref(v_c_733_);
lean_dec(v_x_731_);
v_a_806_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_740_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_740_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_731_ = stack[0].m_obj;
lean_object* v_info_732_ = stack[1].m_obj;
lean_object* v_c_733_ = stack[2].m_obj;
lean_object* v_a_734_ = stack[3].m_obj;
lean_object* v_a_735_ = stack[4].m_obj;
lean_object* v_a_736_ = stack[5].m_obj;
lean_object* v_a_737_ = stack[6].m_obj;
lean_object* v_a_738_ = stack[7].m_obj;
lean_object* v_res_814_;
v_res_814_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_731_, v_info_732_, v_c_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
stack->m_obj
 = v_res_814_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___boxed(lean_object* v_x_815_, lean_object* v_info_816_, lean_object* v_c_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_815_, v_info_816_, v_c_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec_ref(v_a_818_);
lean_dec_ref(v_info_816_);
return v_res_824_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0(lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(v___y_829_);
return v___x_831_;
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_825_ = stack[0].m_obj;
lean_object* v___y_826_ = stack[1].m_obj;
lean_object* v___y_827_ = stack[2].m_obj;
lean_object* v___y_828_ = stack[3].m_obj;
lean_object* v___y_829_ = stack[4].m_obj;
lean_object* v_res_832_;
v_res_832_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0(v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
stack->m_obj
 = v_res_832_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___boxed(lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0(v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec_ref(v___y_833_);
return v_res_839_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(lean_object* v_x_840_, lean_object* v_as_841_, size_t v_i_842_, size_t v_stop_843_){
_start:
{
uint8_t v___x_844_; 
v___x_844_ = lean_usize_dec_eq(v_i_842_, v_stop_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; uint8_t v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_845_ = lean_array_uget_borrowed(v_as_841_, v_i_842_);
v___x_846_ = 1;
lean_inc(v_x_840_);
v___x_847_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_840_);
v___x_848_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(v___x_846_, v___x_845_, v___x_847_);
lean_dec(v___x_847_);
if (v___x_848_ == 0)
{
size_t v___x_849_; size_t v___x_850_; 
v___x_849_ = ((size_t)1ULL);
v___x_850_ = lean_usize_add(v_i_842_, v___x_849_);
v_i_842_ = v___x_850_;
goto _start;
}
else
{
lean_dec(v_x_840_);
return v___x_848_;
}
}
else
{
uint8_t v___x_852_; 
lean_dec(v_x_840_);
v___x_852_ = 0;
return v___x_852_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_840_ = stack[0].m_obj;
lean_object* v_as_841_ = stack[1].m_obj;
size_t v_i_842_ = stack[2].m_num;
size_t v_stop_843_ = stack[3].m_num;
uint8_t v_res_853_;
v_res_853_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(v_x_840_, v_as_841_, v_i_842_, v_stop_843_);
stack->m_num = v_res_853_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0___boxed(lean_object* v_x_854_, lean_object* v_as_855_, lean_object* v_i_856_, lean_object* v_stop_857_){
_start:
{
size_t v_i_boxed_858_; size_t v_stop_boxed_859_; uint8_t v_res_860_; lean_object* v_r_861_; 
v_i_boxed_858_ = lean_unbox_usize(v_i_856_);
lean_dec(v_i_856_);
v_stop_boxed_859_ = lean_unbox_usize(v_stop_857_);
lean_dec(v_stop_857_);
v_res_860_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(v_x_854_, v_as_855_, v_i_boxed_858_, v_stop_boxed_859_);
lean_dec_ref(v_as_855_);
v_r_861_ = lean_box(v_res_860_);
return v_r_861_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(lean_object* v_instr_862_, lean_object* v_x_863_){
_start:
{
if (lean_obj_tag(v_instr_862_) == 0)
{
lean_object* v_decl_864_; lean_object* v_value_865_; 
v_decl_864_ = lean_ctor_get(v_instr_862_, 0);
v_value_865_ = lean_ctor_get(v_decl_864_, 3);
if (lean_obj_tag(v_value_865_) == 5)
{
lean_object* v_args_866_; lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v_args_866_ = lean_ctor_get(v_value_865_, 1);
v___x_867_ = lean_unsigned_to_nat(0u);
v___x_868_ = lean_array_get_size(v_args_866_);
v___x_869_ = lean_nat_dec_lt(v___x_867_, v___x_868_);
if (v___x_869_ == 0)
{
lean_dec(v_x_863_);
return v___x_869_;
}
else
{
if (v___x_869_ == 0)
{
lean_dec(v_x_863_);
return v___x_869_;
}
else
{
size_t v___x_870_; size_t v___x_871_; uint8_t v___x_872_; 
v___x_870_ = ((size_t)0ULL);
v___x_871_ = lean_usize_of_nat(v___x_868_);
v___x_872_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(v_x_863_, v_args_866_, v___x_870_, v___x_871_);
return v___x_872_;
}
}
}
else
{
uint8_t v___x_873_; 
lean_dec(v_x_863_);
v___x_873_ = 0;
return v___x_873_;
}
}
else
{
uint8_t v___x_874_; 
lean_dec(v_x_863_);
v___x_874_ = 0;
return v___x_874_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_0interp(lean_interpreter_value* stack)
{
lean_object* v_instr_862_ = stack[0].m_obj;
lean_object* v_x_863_ = stack[1].m_obj;
uint8_t v_res_875_;
v_res_875_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_862_, v_x_863_);
stack->m_num = v_res_875_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing___boxed(lean_object* v_instr_876_, lean_object* v_x_877_){
_start:
{
uint8_t v_res_878_; lean_object* v_r_879_; 
v_res_878_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_876_, v_x_877_);
lean_dec_ref(v_instr_876_);
v_r_879_ = lean_box(v_res_878_);
return v_r_879_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx___impl(uint8_t v_x_880_){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = lean_box(v_x_880_);
v___x_882_ = lean_obj_tag_nat(v___x_881_);
lean_dec(v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_880_ = stack[0].m_num;
lean_object* v_res_883_;
v_res_883_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx___impl(v_x_880_);
stack->m_obj
 = v_res_883_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx___impl___boxed(lean_object* v_x_884_){
_start:
{
uint8_t v_x_4__boxed_885_; lean_object* v_res_886_; 
v_x_4__boxed_885_ = lean_unbox(v_x_884_);
v_res_886_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx___impl(v_x_4__boxed_885_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg(lean_object* v_k_887_){
_start:
{
lean_inc(v_k_887_);
return v_k_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg___boxed(lean_object* v_k_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg(v_k_888_);
lean_dec(v_k_888_);
return v_res_889_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim(lean_object* v_motive_890_, lean_object* v_ctorIdx_891_, uint8_t v_t_892_, lean_object* v_h_893_, lean_object* v_k_894_){
_start:
{
lean_inc(v_k_894_);
return v_k_894_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_891_ = stack[1].m_obj;
uint8_t v_t_892_ = stack[2].m_num;
lean_object* v_k_894_ = stack[4].m_obj;
lean_object* v_res_895_;
v_res_895_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim(lean_box(0), v_ctorIdx_891_, v_t_892_, lean_box(0), v_k_894_);
stack->m_obj
 = v_res_895_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___boxed(lean_object* v_motive_896_, lean_object* v_ctorIdx_897_, lean_object* v_t_898_, lean_object* v_h_899_, lean_object* v_k_900_){
_start:
{
uint8_t v_t_boxed_901_; lean_object* v_res_902_; 
v_t_boxed_901_ = lean_unbox(v_t_898_);
v_res_902_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim(v_motive_896_, v_ctorIdx_897_, v_t_boxed_901_, v_h_899_, v_k_900_);
lean_dec(v_k_900_);
lean_dec(v_ctorIdx_897_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg(lean_object* v_ownedArg_903_){
_start:
{
lean_inc(v_ownedArg_903_);
return v_ownedArg_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg___boxed(lean_object* v_ownedArg_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg(v_ownedArg_904_);
lean_dec(v_ownedArg_904_);
return v_res_905_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim(lean_object* v_motive_906_, uint8_t v_t_907_, lean_object* v_h_908_, lean_object* v_ownedArg_909_){
_start:
{
lean_inc(v_ownedArg_909_);
return v_ownedArg_909_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_907_ = stack[1].m_num;
lean_object* v_ownedArg_909_ = stack[3].m_obj;
lean_object* v_res_910_;
v_res_910_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim(lean_box(0), v_t_907_, lean_box(0), v_ownedArg_909_);
stack->m_obj
 = v_res_910_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___boxed(lean_object* v_motive_911_, lean_object* v_t_912_, lean_object* v_h_913_, lean_object* v_ownedArg_914_){
_start:
{
uint8_t v_t_boxed_915_; lean_object* v_res_916_; 
v_t_boxed_915_ = lean_unbox(v_t_912_);
v_res_916_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim(v_motive_911_, v_t_boxed_915_, v_h_913_, v_ownedArg_914_);
lean_dec(v_ownedArg_914_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg(lean_object* v_other_917_){
_start:
{
lean_inc(v_other_917_);
return v_other_917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg___boxed(lean_object* v_other_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg(v_other_918_);
lean_dec(v_other_918_);
return v_res_919_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim(lean_object* v_motive_920_, uint8_t v_t_921_, lean_object* v_h_922_, lean_object* v_other_923_){
_start:
{
lean_inc(v_other_923_);
return v_other_923_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_921_ = stack[1].m_num;
lean_object* v_other_923_ = stack[3].m_obj;
lean_object* v_res_924_;
v_res_924_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim(lean_box(0), v_t_921_, lean_box(0), v_other_923_);
stack->m_obj
 = v_res_924_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___boxed(lean_object* v_motive_925_, lean_object* v_t_926_, lean_object* v_h_927_, lean_object* v_other_928_){
_start:
{
uint8_t v_t_boxed_929_; lean_object* v_res_930_; 
v_t_boxed_929_ = lean_unbox(v_t_926_);
v_res_930_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim(v_motive_925_, v_t_boxed_929_, v_h_927_, v_other_928_);
lean_dec(v_other_928_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg(lean_object* v_none_931_){
_start:
{
lean_inc(v_none_931_);
return v_none_931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg___boxed(lean_object* v_none_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg(v_none_932_);
lean_dec(v_none_932_);
return v_res_933_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim(lean_object* v_motive_934_, uint8_t v_t_935_, lean_object* v_h_936_, lean_object* v_none_937_){
_start:
{
lean_inc(v_none_937_);
return v_none_937_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_935_ = stack[1].m_num;
lean_object* v_none_937_ = stack[3].m_obj;
lean_object* v_res_938_;
v_res_938_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim(lean_box(0), v_t_935_, lean_box(0), v_none_937_);
stack->m_obj
 = v_res_938_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___boxed(lean_object* v_motive_939_, lean_object* v_t_940_, lean_object* v_h_941_, lean_object* v_none_942_){
_start:
{
uint8_t v_t_boxed_943_; lean_object* v_res_944_; 
v_t_boxed_943_ = lean_unbox(v_t_940_);
v_res_944_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim(v_motive_939_, v_t_boxed_943_, v_h_941_, v_none_942_);
lean_dec(v_none_942_);
return v_res_944_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(lean_object* v_x_945_, lean_object* v_as_946_, size_t v_sz_947_, size_t v_i_948_, lean_object* v_b_949_){
_start:
{
lean_object* v_a_952_; uint8_t v___x_956_; 
v___x_956_ = lean_usize_dec_lt(v_i_948_, v_sz_947_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; 
v___x_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_957_, 0, v_b_949_);
return v___x_957_;
}
else
{
lean_object* v_snd_958_; lean_object* v_fst_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_1003_; 
v_snd_958_ = lean_ctor_get(v_b_949_, 1);
v_fst_959_ = lean_ctor_get(v_b_949_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_b_949_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_961_ = v_b_949_;
v_isShared_962_ = v_isSharedCheck_1003_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_snd_958_);
lean_inc(v_fst_959_);
lean_dec(v_b_949_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_1003_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v_array_963_; lean_object* v_start_964_; lean_object* v_stop_965_; uint8_t v___x_966_; 
v_array_963_ = lean_ctor_get(v_snd_958_, 0);
v_start_964_ = lean_ctor_get(v_snd_958_, 1);
v_stop_965_ = lean_ctor_get(v_snd_958_, 2);
v___x_966_ = lean_nat_dec_lt(v_start_964_, v_stop_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_968_; 
if (v_isShared_962_ == 0)
{
v___x_968_ = v___x_961_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_fst_959_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_snd_958_);
v___x_968_ = v_reuseFailAlloc_970_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_969_; 
v___x_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
return v___x_969_;
}
}
else
{
lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_999_; 
lean_inc(v_stop_965_);
lean_inc(v_start_964_);
lean_inc_ref(v_array_963_);
v_isSharedCheck_999_ = !lean_is_exclusive(v_snd_958_);
if (v_isSharedCheck_999_ == 0)
{
lean_object* v_unused_1000_; lean_object* v_unused_1001_; lean_object* v_unused_1002_; 
v_unused_1000_ = lean_ctor_get(v_snd_958_, 2);
lean_dec(v_unused_1000_);
v_unused_1001_ = lean_ctor_get(v_snd_958_, 1);
lean_dec(v_unused_1001_);
v_unused_1002_ = lean_ctor_get(v_snd_958_, 0);
lean_dec(v_unused_1002_);
v___x_972_ = v_snd_958_;
v_isShared_973_ = v_isSharedCheck_999_;
goto v_resetjp_971_;
}
else
{
lean_dec(v_snd_958_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_999_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v_a_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_979_; 
v_a_974_ = lean_array_uget_borrowed(v_as_946_, v_i_948_);
v___x_975_ = lean_array_fget(v_array_963_, v_start_964_);
v___x_976_ = lean_unsigned_to_nat(1u);
v___x_977_ = lean_nat_add(v_start_964_, v___x_976_);
lean_dec(v_start_964_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 1, v___x_977_);
v___x_979_ = v___x_972_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_array_963_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v___x_977_);
lean_ctor_set(v_reuseFailAlloc_998_, 2, v_stop_965_);
v___x_979_ = v_reuseFailAlloc_998_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
uint8_t v___y_981_; 
if (lean_obj_tag(v_a_974_) == 1)
{
lean_object* v_fvarId_986_; uint8_t v___x_987_; 
v_fvarId_986_ = lean_ctor_get(v_a_974_, 0);
v___x_987_ = l_Lean_instBEqFVarId_beq(v_fvarId_986_, v_x_945_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; 
lean_dec(v___x_975_);
lean_del_object(v___x_961_);
v___x_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_988_, 0, v_fst_959_);
lean_ctor_set(v___x_988_, 1, v___x_979_);
v_a_952_ = v___x_988_;
goto v___jp_951_;
}
else
{
uint8_t v___x_989_; 
v___x_989_ = lean_unbox(v_fst_959_);
switch(v___x_989_)
{
case 0:
{
uint8_t v_borrow_990_; 
v_borrow_990_ = lean_ctor_get_uint8(v___x_975_, sizeof(void*)*3);
lean_dec(v___x_975_);
if (v_borrow_990_ == 0)
{
uint8_t v___x_991_; 
v___x_991_ = lean_unbox(v_fst_959_);
lean_dec(v_fst_959_);
v___y_981_ = v___x_991_;
goto v___jp_980_;
}
else
{
uint8_t v___x_992_; 
lean_dec(v_fst_959_);
v___x_992_ = 1;
v___y_981_ = v___x_992_;
goto v___jp_980_;
}
}
case 1:
{
uint8_t v___x_993_; 
lean_dec(v___x_975_);
v___x_993_ = lean_unbox(v_fst_959_);
lean_dec(v_fst_959_);
v___y_981_ = v___x_993_;
goto v___jp_980_;
}
default: 
{
uint8_t v_borrow_994_; 
lean_dec(v_fst_959_);
v_borrow_994_ = lean_ctor_get_uint8(v___x_975_, sizeof(void*)*3);
lean_dec(v___x_975_);
if (v_borrow_994_ == 0)
{
uint8_t v___x_995_; 
v___x_995_ = 0;
v___y_981_ = v___x_995_;
goto v___jp_980_;
}
else
{
uint8_t v___x_996_; 
v___x_996_ = 1;
v___y_981_ = v___x_996_;
goto v___jp_980_;
}
}
}
}
}
else
{
lean_object* v___x_997_; 
lean_dec(v___x_975_);
lean_del_object(v___x_961_);
v___x_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_997_, 0, v_fst_959_);
lean_ctor_set(v___x_997_, 1, v___x_979_);
v_a_952_ = v___x_997_;
goto v___jp_951_;
}
v___jp_980_:
{
lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_982_ = lean_box(v___y_981_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 1, v___x_979_);
lean_ctor_set(v___x_961_, 0, v___x_982_);
v___x_984_ = v___x_961_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v___x_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
v_a_952_ = v___x_984_;
goto v___jp_951_;
}
}
}
}
}
}
}
v___jp_951_:
{
size_t v___x_953_; size_t v___x_954_; 
v___x_953_ = ((size_t)1ULL);
v___x_954_ = lean_usize_add(v_i_948_, v___x_953_);
v_i_948_ = v___x_954_;
v_b_949_ = v_a_952_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_945_ = stack[0].m_obj;
lean_object* v_as_946_ = stack[1].m_obj;
size_t v_sz_947_ = stack[2].m_num;
size_t v_i_948_ = stack[3].m_num;
lean_object* v_b_949_ = stack[4].m_obj;
lean_object* v_res_1004_;
v_res_1004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(v_x_945_, v_as_946_, v_sz_947_, v_i_948_, v_b_949_);
stack->m_obj
 = v_res_1004_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg___boxed(lean_object* v_x_1005_, lean_object* v_as_1006_, lean_object* v_sz_1007_, lean_object* v_i_1008_, lean_object* v_b_1009_, lean_object* v___y_1010_){
_start:
{
size_t v_sz_boxed_1011_; size_t v_i_boxed_1012_; lean_object* v_res_1013_; 
v_sz_boxed_1011_ = lean_unbox_usize(v_sz_1007_);
lean_dec(v_sz_1007_);
v_i_boxed_1012_ = lean_unbox_usize(v_i_1008_);
lean_dec(v_i_1008_);
v_res_1013_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(v_x_1005_, v_as_1006_, v_sz_boxed_1011_, v_i_boxed_1012_, v_b_1009_);
lean_dec_ref(v_as_1006_);
lean_dec(v_x_1005_);
return v_res_1013_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(lean_object* v_instr_1014_, lean_object* v_x_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
if (lean_obj_tag(v_instr_1014_) == 0)
{
lean_object* v_decl_1032_; lean_object* v_value_1033_; 
v_decl_1032_ = lean_ctor_get(v_instr_1014_, 0);
v_value_1033_ = lean_ctor_get(v_decl_1032_, 3);
lean_inc(v_value_1033_);
switch(lean_obj_tag(v_value_1033_))
{
case 9:
{
lean_object* v_fn_1034_; lean_object* v_args_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1097_; 
lean_dec_ref_known(v_instr_1014_, 1);
v_fn_1034_ = lean_ctor_get(v_value_1033_, 0);
v_args_1035_ = lean_ctor_get(v_value_1033_, 1);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_value_1033_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1037_ = v_value_1033_;
v_isShared_1038_ = v_isSharedCheck_1097_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_args_1035_);
lean_inc(v_fn_1034_);
lean_dec(v_value_1033_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1097_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
uint8_t v___x_1039_; lean_object* v___x_1041_; 
v___x_1039_ = 1;
lean_inc_ref(v_args_1035_);
lean_inc(v_fn_1034_);
if (v_isShared_1038_ == 0)
{
v___x_1041_ = v___x_1037_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_fn_1034_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_args_1035_);
v___x_1041_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_1034_, v_a_1020_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1087_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1045_ = v___x_1042_;
v_isShared_1046_ = v_isSharedCheck_1087_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1087_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
if (lean_obj_tag(v_a_1043_) == 1)
{
lean_object* v_val_1047_; lean_object* v_params_1048_; uint8_t v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; size_t v_sz_1055_; size_t v___x_1056_; lean_object* v___x_1057_; 
lean_del_object(v___x_1045_);
lean_dec_ref(v___x_1041_);
v_val_1047_ = lean_ctor_get(v_a_1043_, 0);
lean_inc(v_val_1047_);
lean_dec_ref_known(v_a_1043_, 1);
v_params_1048_ = lean_ctor_get(v_val_1047_, 3);
lean_inc_ref(v_params_1048_);
lean_dec(v_val_1047_);
v___x_1049_ = 2;
v___x_1050_ = lean_unsigned_to_nat(0u);
v___x_1051_ = lean_array_get_size(v_params_1048_);
v___x_1052_ = l_Array_toSubarray___redArg(v_params_1048_, v___x_1050_, v___x_1051_);
v___x_1053_ = lean_box(v___x_1049_);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v___x_1052_);
v_sz_1055_ = lean_array_size(v_args_1035_);
v___x_1056_ = ((size_t)0ULL);
v___x_1057_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(v_x_1015_, v_args_1035_, v_sz_1055_, v___x_1056_, v___x_1054_);
lean_dec_ref(v_args_1035_);
lean_dec(v_x_1015_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1066_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1060_ = v___x_1057_;
v_isShared_1061_ = v_isSharedCheck_1066_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1057_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1066_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v_fst_1062_; lean_object* v___x_1064_; 
v_fst_1062_ = lean_ctor_get(v_a_1058_, 0);
lean_inc(v_fst_1062_);
lean_dec(v_a_1058_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 0, v_fst_1062_);
v___x_1064_ = v___x_1060_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_fst_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
v_a_1067_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1057_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1057_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
else
{
lean_object* v___x_1075_; uint8_t v___x_1076_; 
lean_dec(v_a_1043_);
lean_dec_ref(v_args_1035_);
v___x_1075_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_1015_);
v___x_1076_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v___x_1039_, v___x_1041_, v___x_1075_);
lean_dec(v___x_1075_);
lean_dec_ref(v___x_1041_);
if (v___x_1076_ == 0)
{
uint8_t v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1077_ = 2;
v___x_1078_ = lean_box(v___x_1077_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v___x_1078_);
v___x_1080_ = v___x_1045_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
else
{
uint8_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1082_ = 0;
v___x_1083_ = lean_box(v___x_1082_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v___x_1083_);
v___x_1085_ = v___x_1045_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec_ref(v___x_1041_);
lean_dec_ref(v_args_1035_);
lean_dec(v_x_1015_);
v_a_1088_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1042_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1042_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
}
case 10:
{
lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1123_; 
v_isSharedCheck_1123_ = !lean_is_exclusive(v_instr_1014_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; 
v_unused_1124_ = lean_ctor_get(v_instr_1014_, 0);
lean_dec(v_unused_1124_);
v___x_1099_ = v_instr_1014_;
v_isShared_1100_ = v_isSharedCheck_1123_;
goto v_resetjp_1098_;
}
else
{
lean_dec(v_instr_1014_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1123_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v_fn_1101_; lean_object* v_args_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1122_; 
v_fn_1101_ = lean_ctor_get(v_value_1033_, 0);
v_args_1102_ = lean_ctor_get(v_value_1033_, 1);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_value_1033_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1104_ = v_value_1033_;
v_isShared_1105_ = v_isSharedCheck_1122_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_args_1102_);
lean_inc(v_fn_1101_);
lean_dec(v_value_1033_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1122_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
uint8_t v___x_1106_; lean_object* v___x_1108_; 
v___x_1106_ = 1;
if (v_isShared_1105_ == 0)
{
v___x_1108_ = v___x_1104_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_fn_1101_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_args_1102_);
v___x_1108_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1109_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_1015_);
v___x_1110_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v___x_1106_, v___x_1108_, v___x_1109_);
lean_dec(v___x_1109_);
lean_dec_ref(v___x_1108_);
if (v___x_1110_ == 0)
{
uint8_t v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1111_ = 2;
v___x_1112_ = lean_box(v___x_1111_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v___x_1112_);
v___x_1114_ = v___x_1099_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
else
{
uint8_t v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1116_ = 0;
v___x_1117_ = lean_box(v___x_1116_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v___x_1117_);
v___x_1119_ = v___x_1099_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1117_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
}
case 4:
{
lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1150_; 
v_isSharedCheck_1150_ = !lean_is_exclusive(v_instr_1014_);
if (v_isSharedCheck_1150_ == 0)
{
lean_object* v_unused_1151_; 
v_unused_1151_ = lean_ctor_get(v_instr_1014_, 0);
lean_dec(v_unused_1151_);
v___x_1126_ = v_instr_1014_;
v_isShared_1127_ = v_isSharedCheck_1150_;
goto v_resetjp_1125_;
}
else
{
lean_dec(v_instr_1014_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1150_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v_fvarId_1128_; lean_object* v_args_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1149_; 
v_fvarId_1128_ = lean_ctor_get(v_value_1033_, 0);
v_args_1129_ = lean_ctor_get(v_value_1033_, 1);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_value_1033_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1131_ = v_value_1033_;
v_isShared_1132_ = v_isSharedCheck_1149_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_args_1129_);
lean_inc(v_fvarId_1128_);
lean_dec(v_value_1033_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1149_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
uint8_t v___x_1133_; lean_object* v___x_1135_; 
v___x_1133_ = 1;
if (v_isShared_1132_ == 0)
{
v___x_1135_ = v___x_1131_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_fvarId_1128_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_args_1129_);
v___x_1135_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1136_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_1015_);
v___x_1137_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v___x_1133_, v___x_1135_, v___x_1136_);
lean_dec(v___x_1136_);
lean_dec_ref(v___x_1135_);
if (v___x_1137_ == 0)
{
uint8_t v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1138_ = 2;
v___x_1139_ = lean_box(v___x_1138_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1139_);
v___x_1141_ = v___x_1126_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
else
{
uint8_t v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1143_ = 0;
v___x_1144_ = lean_box(v___x_1143_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1144_);
v___x_1146_ = v___x_1126_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
}
default: 
{
lean_dec(v_value_1033_);
goto v___jp_1022_;
}
}
}
else
{
goto v___jp_1022_;
}
v___jp_1022_:
{
uint8_t v___x_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v___x_1023_ = 1;
v___x_1024_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_1015_);
v___x_1025_ = l_Lean_Compiler_LCNF_CodeDecl_dependsOn(v___x_1023_, v_instr_1014_, v___x_1024_);
lean_dec(v___x_1024_);
lean_dec_ref(v_instr_1014_);
if (v___x_1025_ == 0)
{
uint8_t v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1026_ = 2;
v___x_1027_ = lean_box(v___x_1026_);
v___x_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
return v___x_1028_;
}
else
{
uint8_t v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1029_ = 1;
v___x_1030_ = lean_box(v___x_1029_);
v___x_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
return v___x_1031_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_0interp(lean_interpreter_value* stack)
{
lean_object* v_instr_1014_ = stack[0].m_obj;
lean_object* v_x_1015_ = stack[1].m_obj;
lean_object* v_a_1016_ = stack[2].m_obj;
lean_object* v_a_1017_ = stack[3].m_obj;
lean_object* v_a_1018_ = stack[4].m_obj;
lean_object* v_a_1019_ = stack[5].m_obj;
lean_object* v_a_1020_ = stack[6].m_obj;
lean_object* v_res_1152_;
v_res_1152_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1014_, v_x_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
stack->m_obj
 = v_res_1152_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse___boxed(lean_object* v_instr_1153_, lean_object* v_x_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1153_, v_x_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec_ref(v_a_1155_);
return v_res_1161_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0(lean_object* v_x_1162_, lean_object* v_as_1163_, size_t v_sz_1164_, size_t v_i_1165_, lean_object* v_b_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(v_x_1162_, v_as_1163_, v_sz_1164_, v_i_1165_, v_b_1166_);
return v___x_1173_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1162_ = stack[0].m_obj;
lean_object* v_as_1163_ = stack[1].m_obj;
size_t v_sz_1164_ = stack[2].m_num;
size_t v_i_1165_ = stack[3].m_num;
lean_object* v_b_1166_ = stack[4].m_obj;
lean_object* v___y_1167_ = stack[5].m_obj;
lean_object* v___y_1168_ = stack[6].m_obj;
lean_object* v___y_1169_ = stack[7].m_obj;
lean_object* v___y_1170_ = stack[8].m_obj;
lean_object* v___y_1171_ = stack[9].m_obj;
lean_object* v_res_1174_;
v_res_1174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0(v_x_1162_, v_as_1163_, v_sz_1164_, v_i_1165_, v_b_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
stack->m_obj
 = v_res_1174_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___boxed(lean_object* v_x_1175_, lean_object* v_as_1176_, lean_object* v_sz_1177_, lean_object* v_i_1178_, lean_object* v_b_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
size_t v_sz_boxed_1186_; size_t v_i_boxed_1187_; lean_object* v_res_1188_; 
v_sz_boxed_1186_ = lean_unbox_usize(v_sz_1177_);
lean_dec(v_sz_1177_);
v_i_boxed_1187_ = lean_unbox_usize(v_i_1178_);
lean_dec(v_i_1178_);
v_res_1188_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0(v_x_1175_, v_as_1176_, v_sz_boxed_1186_, v_i_boxed_1187_, v_b_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec_ref(v_as_1176_);
lean_dec(v_x_1175_);
return v_res_1188_;
}
}
lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(lean_object* v_alt_1189_, lean_object* v_f_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v___y_1198_; 
switch(lean_obj_tag(v_alt_1189_))
{
case 0:
{
lean_object* v_code_1217_; 
v_code_1217_ = lean_ctor_get(v_alt_1189_, 2);
lean_inc_ref(v_code_1217_);
v___y_1198_ = v_code_1217_;
goto v___jp_1197_;
}
case 1:
{
lean_object* v_code_1218_; 
v_code_1218_ = lean_ctor_get(v_alt_1189_, 1);
lean_inc_ref(v_code_1218_);
v___y_1198_ = v_code_1218_;
goto v___jp_1197_;
}
default: 
{
lean_object* v_code_1219_; 
v_code_1219_ = lean_ctor_get(v_alt_1189_, 0);
lean_inc_ref(v_code_1219_);
v___y_1198_ = v_code_1219_;
goto v___jp_1197_;
}
}
v___jp_1197_:
{
lean_object* v___x_1199_; 
lean_inc(v___y_1195_);
lean_inc_ref(v___y_1194_);
lean_inc(v___y_1193_);
lean_inc_ref(v___y_1192_);
lean_inc_ref(v___y_1191_);
v___x_1199_ = lean_apply_7(v_f_1190_, v___y_1198_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, lean_box(0));
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1208_; 
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1202_ = v___x_1199_;
v_isShared_1203_ = v_isSharedCheck_1208_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1199_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1208_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1204_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_1189_, v_a_1200_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v___x_1204_);
v___x_1206_ = v___x_1202_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec_ref(v_alt_1189_);
v_a_1209_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1199_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1199_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_alt_1189_ = stack[0].m_obj;
lean_object* v_f_1190_ = stack[1].m_obj;
lean_object* v___y_1191_ = stack[2].m_obj;
lean_object* v___y_1192_ = stack[3].m_obj;
lean_object* v___y_1193_ = stack[4].m_obj;
lean_object* v___y_1194_ = stack[5].m_obj;
lean_object* v___y_1195_ = stack[6].m_obj;
lean_object* v_res_1220_;
v_res_1220_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_alt_1189_, v_f_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
stack->m_obj
 = v_res_1220_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg___boxed(lean_object* v_alt_1221_, lean_object* v_f_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_alt_1221_, v_f_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v___y_1223_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D___boxed(lean_object* v_x_1230_, lean_object* v_info_1231_, lean_object* v_c_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(v_x_1230_, v_info_1231_, v_c_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
lean_dec_ref(v_a_1233_);
return v_res_1239_;
}
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(lean_object* v_x_1240_, lean_object* v_info_1241_, lean_object* v_i_1242_, lean_object* v_as_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1250_ = lean_array_get_size(v_as_1243_);
v___x_1251_ = lean_nat_dec_lt(v_i_1242_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; 
lean_dec(v_i_1242_);
lean_dec_ref(v_info_1241_);
lean_dec(v_x_1240_);
v___x_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1252_, 0, v_as_1243_);
return v___x_1252_;
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v_a_1253_ = lean_array_fget_borrowed(v_as_1243_, v_i_1242_);
lean_inc_ref(v_info_1241_);
lean_inc(v_x_1240_);
v___x_1254_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D___boxed), 9, 2);
lean_closure_set(v___x_1254_, 0, v_x_1240_);
lean_closure_set(v___x_1254_, 1, v_info_1241_);
lean_inc(v_a_1253_);
v___x_1255_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_a_1253_, v___x_1254_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; size_t v___x_1257_; size_t v___x_1258_; uint8_t v___x_1259_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1256_);
lean_dec_ref_known(v___x_1255_, 1);
v___x_1257_ = lean_ptr_addr(v_a_1253_);
v___x_1258_ = lean_ptr_addr(v_a_1256_);
v___x_1259_ = lean_usize_dec_eq(v___x_1257_, v___x_1258_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1260_ = lean_unsigned_to_nat(1u);
v___x_1261_ = lean_nat_add(v_i_1242_, v___x_1260_);
v___x_1262_ = lean_array_fset(v_as_1243_, v_i_1242_, v_a_1256_);
lean_dec(v_i_1242_);
v_i_1242_ = v___x_1261_;
v_as_1243_ = v___x_1262_;
goto _start;
}
else
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
lean_dec(v_a_1256_);
v___x_1264_ = lean_unsigned_to_nat(1u);
v___x_1265_ = lean_nat_add(v_i_1242_, v___x_1264_);
lean_dec(v_i_1242_);
v_i_1242_ = v___x_1265_;
goto _start;
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec_ref(v_as_1243_);
lean_dec(v_i_1242_);
lean_dec_ref(v_info_1241_);
lean_dec(v_x_1240_);
v_a_1267_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1255_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1255_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1240_ = stack[0].m_obj;
lean_object* v_info_1241_ = stack[1].m_obj;
lean_object* v_i_1242_ = stack[2].m_obj;
lean_object* v_as_1243_ = stack[3].m_obj;
lean_object* v___y_1244_ = stack[4].m_obj;
lean_object* v___y_1245_ = stack[5].m_obj;
lean_object* v___y_1246_ = stack[6].m_obj;
lean_object* v___y_1247_ = stack[7].m_obj;
lean_object* v___y_1248_ = stack[8].m_obj;
lean_object* v_res_1275_;
v_res_1275_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(v_x_1240_, v_info_1241_, v_i_1242_, v_as_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
stack->m_obj
 = v_res_1275_;
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1277_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_1278_ = lean_unsigned_to_nat(61u);
v___x_1279_ = lean_unsigned_to_nat(247u);
v___x_1280_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__0));
v___x_1281_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_1282_ = l_mkPanicMessageWithDecl(v___x_1281_, v___x_1280_, v___x_1279_, v___x_1278_, v___x_1277_);
return v___x_1282_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(lean_object* v_x_1283_, lean_object* v_info_1284_, lean_object* v_c_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
switch(lean_obj_tag(v_c_1285_))
{
case 0:
{
lean_object* v_decl_1292_; lean_object* v_k_1293_; uint8_t v___x_1294_; lean_object* v_instr_1295_; uint8_t v___x_1296_; uint8_t v___x_1297_; 
v_decl_1292_ = lean_ctor_get(v_c_1285_, 0);
v_k_1293_ = lean_ctor_get(v_c_1285_, 1);
v___x_1294_ = 1;
v_instr_1295_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_1294_, v_c_1285_);
lean_inc(v_x_1283_);
v___x_1296_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_1295_, v_x_1283_);
v___x_1297_ = 1;
if (v___x_1296_ == 0)
{
lean_object* v___x_1298_; 
lean_inc_ref(v_k_1293_);
lean_inc_ref(v_info_1284_);
lean_inc(v_x_1283_);
v___x_1298_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1283_, v_info_1284_, v_k_1293_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1416_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1301_ = v___x_1298_;
v_isShared_1302_ = v_isSharedCheck_1416_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1298_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1416_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___y_1304_; lean_object* v_snd_1310_; uint8_t v___x_1311_; 
v_snd_1310_ = lean_ctor_get(v_a_1299_, 1);
v___x_1311_ = lean_unbox(v_snd_1310_);
if (v___x_1311_ == 0)
{
lean_object* v_fst_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1401_; 
lean_inc(v_snd_1310_);
lean_del_object(v___x_1301_);
v_fst_1312_ = lean_ctor_get(v_a_1299_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_a_1299_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; 
v_unused_1402_ = lean_ctor_get(v_a_1299_, 1);
lean_dec(v_unused_1402_);
v___x_1314_ = v_a_1299_;
v_isShared_1315_ = v_isSharedCheck_1401_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_fst_1312_);
lean_dec(v_a_1299_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1401_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1316_; 
lean_inc(v_x_1283_);
v___x_1316_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1295_, v_x_1283_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1392_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1319_ = v___x_1316_;
v_isShared_1320_ = v_isSharedCheck_1392_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1392_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___y_1322_; lean_object* v___y_1330_; uint8_t v___x_1334_; 
v___x_1334_ = lean_unbox(v_a_1317_);
lean_dec(v_a_1317_);
switch(v___x_1334_)
{
case 0:
{
size_t v___x_1335_; size_t v___x_1336_; uint8_t v___x_1337_; 
lean_del_object(v___x_1319_);
lean_del_object(v___x_1314_);
lean_dec(v_snd_1310_);
lean_dec_ref(v_info_1284_);
lean_dec(v_x_1283_);
v___x_1335_ = lean_ptr_addr(v_k_1293_);
v___x_1336_ = lean_ptr_addr(v_fst_1312_);
v___x_1337_ = lean_usize_dec_eq(v___x_1335_, v___x_1336_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
lean_inc_ref(v_decl_1292_);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_c_1285_);
if (v_isSharedCheck_1344_ == 0)
{
lean_object* v_unused_1345_; lean_object* v_unused_1346_; 
v_unused_1345_ = lean_ctor_get(v_c_1285_, 1);
lean_dec(v_unused_1345_);
v_unused_1346_ = lean_ctor_get(v_c_1285_, 0);
lean_dec(v_unused_1346_);
v___x_1339_ = v_c_1285_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_dec(v_c_1285_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 1, v_fst_1312_);
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_decl_1292_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_fst_1312_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
v___y_1330_ = v___x_1342_;
goto v___jp_1329_;
}
}
}
else
{
lean_dec(v_fst_1312_);
v___y_1330_ = v_c_1285_;
goto v___jp_1329_;
}
}
case 1:
{
lean_object* v___x_1347_; 
lean_del_object(v___x_1319_);
lean_del_object(v___x_1314_);
lean_dec(v_snd_1310_);
v___x_1347_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_1283_, v_info_1284_, v_fst_1312_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec_ref(v_info_1284_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1371_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1350_ = v___x_1347_;
v_isShared_1351_ = v_isSharedCheck_1371_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1347_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1371_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___y_1353_; size_t v___x_1359_; size_t v___x_1360_; uint8_t v___x_1361_; 
v___x_1359_ = lean_ptr_addr(v_k_1293_);
v___x_1360_ = lean_ptr_addr(v_a_1348_);
v___x_1361_ = lean_usize_dec_eq(v___x_1359_, v___x_1360_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_inc_ref(v_decl_1292_);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_c_1285_);
if (v_isSharedCheck_1368_ == 0)
{
lean_object* v_unused_1369_; lean_object* v_unused_1370_; 
v_unused_1369_ = lean_ctor_get(v_c_1285_, 1);
lean_dec(v_unused_1369_);
v_unused_1370_ = lean_ctor_get(v_c_1285_, 0);
lean_dec(v_unused_1370_);
v___x_1363_ = v_c_1285_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_dec(v_c_1285_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 1, v_a_1348_);
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_decl_1292_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_a_1348_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
v___y_1353_ = v___x_1366_;
goto v___jp_1352_;
}
}
}
else
{
lean_dec(v_a_1348_);
v___y_1353_ = v_c_1285_;
goto v___jp_1352_;
}
v___jp_1352_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1354_ = lean_box(v___x_1297_);
v___x_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___y_1353_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v___x_1355_);
v___x_1357_ = v___x_1350_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1355_);
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
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_dec_ref_known(v_c_1285_, 2);
v_a_1372_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1347_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1347_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
default: 
{
size_t v___x_1380_; size_t v___x_1381_; uint8_t v___x_1382_; 
lean_dec_ref(v_info_1284_);
lean_dec(v_x_1283_);
v___x_1380_ = lean_ptr_addr(v_k_1293_);
v___x_1381_ = lean_ptr_addr(v_fst_1312_);
v___x_1382_ = lean_usize_dec_eq(v___x_1380_, v___x_1381_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_inc_ref(v_decl_1292_);
v_isSharedCheck_1389_ = !lean_is_exclusive(v_c_1285_);
if (v_isSharedCheck_1389_ == 0)
{
lean_object* v_unused_1390_; lean_object* v_unused_1391_; 
v_unused_1390_ = lean_ctor_get(v_c_1285_, 1);
lean_dec(v_unused_1390_);
v_unused_1391_ = lean_ctor_get(v_c_1285_, 0);
lean_dec(v_unused_1391_);
v___x_1384_ = v_c_1285_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_dec(v_c_1285_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 1, v_fst_1312_);
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_decl_1292_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_fst_1312_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
v___y_1322_ = v___x_1387_;
goto v___jp_1321_;
}
}
}
else
{
lean_dec(v_fst_1312_);
v___y_1322_ = v_c_1285_;
goto v___jp_1321_;
}
}
}
v___jp_1321_:
{
lean_object* v___x_1324_; 
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v___y_1322_);
v___x_1324_ = v___x_1314_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___y_1322_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v_snd_1310_);
v___x_1324_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
lean_object* v___x_1326_; 
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v___x_1324_);
v___x_1326_ = v___x_1319_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
v___jp_1329_:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1331_ = lean_box(v___x_1297_);
v___x_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___y_1330_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
v___x_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
return v___x_1333_;
}
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_del_object(v___x_1314_);
lean_dec(v_fst_1312_);
lean_dec(v_snd_1310_);
lean_dec_ref_known(v_c_1285_, 2);
lean_dec_ref(v_info_1284_);
lean_dec(v_x_1283_);
v_a_1393_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1316_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1316_);
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
else
{
lean_object* v_fst_1403_; size_t v___x_1404_; size_t v___x_1405_; uint8_t v___x_1406_; 
lean_dec_ref(v_instr_1295_);
lean_dec_ref(v_info_1284_);
lean_dec(v_x_1283_);
v_fst_1403_ = lean_ctor_get(v_a_1299_, 0);
lean_inc(v_fst_1403_);
lean_dec(v_a_1299_);
v___x_1404_ = lean_ptr_addr(v_k_1293_);
v___x_1405_ = lean_ptr_addr(v_fst_1403_);
v___x_1406_ = lean_usize_dec_eq(v___x_1404_, v___x_1405_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
lean_inc_ref(v_decl_1292_);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_c_1285_);
if (v_isSharedCheck_1413_ == 0)
{
lean_object* v_unused_1414_; lean_object* v_unused_1415_; 
v_unused_1414_ = lean_ctor_get(v_c_1285_, 1);
lean_dec(v_unused_1414_);
v_unused_1415_ = lean_ctor_get(v_c_1285_, 0);
lean_dec(v_unused_1415_);
v___x_1408_ = v_c_1285_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_dec(v_c_1285_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 1, v_fst_1403_);
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_decl_1292_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_fst_1403_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
v___y_1304_ = v___x_1411_;
goto v___jp_1303_;
}
}
}
else
{
lean_dec(v_fst_1403_);
v___y_1304_ = v_c_1285_;
goto v___jp_1303_;
}
}
v___jp_1303_:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1308_; 
v___x_1305_ = lean_box(v___x_1297_);
v___x_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___y_1304_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1306_);
v___x_1308_ = v___x_1301_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
else
{
lean_dec_ref(v_instr_1295_);
lean_dec_ref_known(v_c_1285_, 2);
lean_dec_ref(v_info_1284_);
lean_dec(v_x_1283_);
return v___x_1298_;
}
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
lean_dec_ref(v_instr_1295_);
lean_dec_ref(v_info_1284_);
lean_dec(v_x_1283_);
v___x_1417_ = lean_box(v___x_1297_);
v___x_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1418_, 0, v_c_1285_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
return v___x_1419_;
}
}
case 2:
{
lean_object* v_decl_1420_; lean_object* v_k_1421_; lean_object* v___x_1422_; 
v_decl_1420_ = lean_ctor_get(v_c_1285_, 0);
v_k_1421_ = lean_ctor_get(v_c_1285_, 1);
lean_inc_ref(v_k_1421_);
lean_inc_ref(v_info_1284_);
lean_inc(v_x_1283_);
v___x_1422_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1283_, v_info_1284_, v_k_1421_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v_fst_1424_; lean_object* v_snd_1425_; lean_object* v_params_1426_; lean_object* v_type_1427_; lean_object* v_value_1428_; uint8_t v___x_1429_; lean_object* v___x_1430_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1422_, 1);
v_fst_1424_ = lean_ctor_get(v_a_1423_, 0);
lean_inc(v_fst_1424_);
v_snd_1425_ = lean_ctor_get(v_a_1423_, 1);
lean_inc(v_snd_1425_);
lean_dec(v_a_1423_);
v_params_1426_ = lean_ctor_get(v_decl_1420_, 2);
v_type_1427_ = lean_ctor_get(v_decl_1420_, 3);
v_value_1428_ = lean_ctor_get(v_decl_1420_, 4);
v___x_1429_ = 1;
lean_inc_ref(v_value_1428_);
v___x_1430_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1283_, v_info_1284_, v_value_1428_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v_fst_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1482_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v_fst_1432_ = lean_ctor_get(v_a_1431_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_a_1431_);
if (v_isSharedCheck_1482_ == 0)
{
lean_object* v_unused_1483_; 
v_unused_1483_ = lean_ctor_get(v_a_1431_, 1);
lean_dec(v_unused_1483_);
v___x_1434_ = v_a_1431_;
v_isShared_1435_ = v_isSharedCheck_1482_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_fst_1432_);
lean_dec(v_a_1431_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1482_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; 
lean_inc_ref(v_params_1426_);
lean_inc_ref(v_type_1427_);
lean_inc_ref(v_decl_1420_);
v___x_1436_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1429_, v_decl_1420_, v_type_1427_, v_params_1426_, v_fst_1432_, v_a_1288_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1473_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1473_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1473_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___y_1442_; size_t v___x_1449_; size_t v___x_1450_; uint8_t v___x_1451_; 
v___x_1449_ = lean_ptr_addr(v_k_1421_);
v___x_1450_ = lean_ptr_addr(v_fst_1424_);
v___x_1451_ = lean_usize_dec_eq(v___x_1449_, v___x_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
v_isSharedCheck_1458_ = !lean_is_exclusive(v_c_1285_);
if (v_isSharedCheck_1458_ == 0)
{
lean_object* v_unused_1459_; lean_object* v_unused_1460_; 
v_unused_1459_ = lean_ctor_get(v_c_1285_, 1);
lean_dec(v_unused_1459_);
v_unused_1460_ = lean_ctor_get(v_c_1285_, 0);
lean_dec(v_unused_1460_);
v___x_1453_ = v_c_1285_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_dec(v_c_1285_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 1, v_fst_1424_);
lean_ctor_set(v___x_1453_, 0, v_a_1437_);
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1437_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_fst_1424_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
v___y_1442_ = v___x_1456_;
goto v___jp_1441_;
}
}
}
else
{
size_t v___x_1461_; size_t v___x_1462_; uint8_t v___x_1463_; 
v___x_1461_ = lean_ptr_addr(v_decl_1420_);
v___x_1462_ = lean_ptr_addr(v_a_1437_);
v___x_1463_ = lean_usize_dec_eq(v___x_1461_, v___x_1462_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
v_isSharedCheck_1470_ = !lean_is_exclusive(v_c_1285_);
if (v_isSharedCheck_1470_ == 0)
{
lean_object* v_unused_1471_; lean_object* v_unused_1472_; 
v_unused_1471_ = lean_ctor_get(v_c_1285_, 1);
lean_dec(v_unused_1471_);
v_unused_1472_ = lean_ctor_get(v_c_1285_, 0);
lean_dec(v_unused_1472_);
v___x_1465_ = v_c_1285_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_dec(v_c_1285_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 1, v_fst_1424_);
lean_ctor_set(v___x_1465_, 0, v_a_1437_);
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1437_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_fst_1424_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
v___y_1442_ = v___x_1468_;
goto v___jp_1441_;
}
}
}
else
{
lean_dec(v_a_1437_);
lean_dec(v_fst_1424_);
v___y_1442_ = v_c_1285_;
goto v___jp_1441_;
}
}
v___jp_1441_:
{
lean_object* v___x_1444_; 
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 1, v_snd_1425_);
lean_ctor_set(v___x_1434_, 0, v___y_1442_);
v___x_1444_ = v___x_1434_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___y_1442_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_snd_1425_);
v___x_1444_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1446_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v___x_1444_);
v___x_1446_ = v___x_1439_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
lean_del_object(v___x_1434_);
lean_dec(v_snd_1425_);
lean_dec(v_fst_1424_);
lean_dec_ref_known(v_c_1285_, 2);
v_a_1474_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1436_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1436_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
}
else
{
lean_dec(v_snd_1425_);
lean_dec(v_fst_1424_);
lean_dec_ref_known(v_c_1285_, 2);
return v___x_1430_;
}
}
else
{
lean_dec_ref_known(v_c_1285_, 2);
lean_dec_ref(v_info_1284_);
lean_dec(v_x_1283_);
return v___x_1422_;
}
}
case 3:
{
lean_object* v___x_1484_; 
lean_dec_ref(v_info_1284_);
lean_inc_ref(v_c_1285_);
v___x_1484_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_1285_, v_x_1283_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1493_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1493_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1493_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v_c_1285_);
lean_ctor_set(v___x_1489_, 1, v_a_1485_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 0, v___x_1489_);
v___x_1491_ = v___x_1487_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1489_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
lean_dec_ref_known(v_c_1285_, 2);
v_a_1494_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1484_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1484_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
case 4:
{
lean_object* v_cases_1502_; lean_object* v___x_1503_; 
v_cases_1502_ = lean_ctor_get(v_c_1285_, 0);
lean_inc_ref(v_cases_1502_);
lean_inc(v_x_1283_);
lean_inc_ref(v_c_1285_);
v___x_1503_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_1285_, v_x_1283_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1556_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1506_ = v___x_1503_;
v_isShared_1507_ = v_isSharedCheck_1556_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1503_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1556_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
uint8_t v___x_1508_; 
v___x_1508_ = lean_unbox(v_a_1504_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; lean_object* v___x_1511_; 
lean_dec_ref(v_cases_1502_);
lean_dec_ref(v_info_1284_);
lean_dec(v_x_1283_);
v___x_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1509_, 0, v_c_1285_);
lean_ctor_set(v___x_1509_, 1, v_a_1504_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v___x_1509_);
v___x_1511_ = v___x_1506_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1509_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
else
{
lean_object* v_typeName_1513_; lean_object* v_resultType_1514_; lean_object* v_discr_1515_; lean_object* v_alts_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1555_; 
lean_del_object(v___x_1506_);
v_typeName_1513_ = lean_ctor_get(v_cases_1502_, 0);
v_resultType_1514_ = lean_ctor_get(v_cases_1502_, 1);
v_discr_1515_ = lean_ctor_get(v_cases_1502_, 2);
v_alts_1516_ = lean_ctor_get(v_cases_1502_, 3);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_cases_1502_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1518_ = v_cases_1502_;
v_isShared_1519_ = v_isSharedCheck_1555_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_alts_1516_);
lean_inc(v_discr_1515_);
lean_inc(v_resultType_1514_);
lean_inc(v_typeName_1513_);
lean_dec(v_cases_1502_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1555_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1516_);
v___x_1521_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(v_x_1283_, v_info_1284_, v___x_1520_, v_alts_1516_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1546_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1524_ = v___x_1521_;
v_isShared_1525_ = v_isSharedCheck_1546_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1521_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1546_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___y_1527_; size_t v___x_1532_; size_t v___x_1533_; uint8_t v___x_1534_; 
v___x_1532_ = lean_ptr_addr(v_alts_1516_);
lean_dec_ref(v_alts_1516_);
v___x_1533_ = lean_ptr_addr(v_a_1522_);
v___x_1534_ = lean_usize_dec_eq(v___x_1532_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1544_; 
v_isSharedCheck_1544_ = !lean_is_exclusive(v_c_1285_);
if (v_isSharedCheck_1544_ == 0)
{
lean_object* v_unused_1545_; 
v_unused_1545_ = lean_ctor_get(v_c_1285_, 0);
lean_dec(v_unused_1545_);
v___x_1536_ = v_c_1285_;
v_isShared_1537_ = v_isSharedCheck_1544_;
goto v_resetjp_1535_;
}
else
{
lean_dec(v_c_1285_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1544_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 3, v_a_1522_);
v___x_1539_ = v___x_1518_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_typeName_1513_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_resultType_1514_);
lean_ctor_set(v_reuseFailAlloc_1543_, 2, v_discr_1515_);
lean_ctor_set(v_reuseFailAlloc_1543_, 3, v_a_1522_);
v___x_1539_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
lean_object* v___x_1541_; 
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v___x_1539_);
v___x_1541_ = v___x_1536_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1539_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
v___y_1527_ = v___x_1541_;
goto v___jp_1526_;
}
}
}
}
else
{
lean_dec(v_a_1522_);
lean_del_object(v___x_1518_);
lean_dec(v_discr_1515_);
lean_dec_ref(v_resultType_1514_);
lean_dec(v_typeName_1513_);
v___y_1527_ = v_c_1285_;
goto v___jp_1526_;
}
v___jp_1526_:
{
lean_object* v___x_1528_; lean_object* v___x_1530_; 
v___x_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___y_1527_);
lean_ctor_set(v___x_1528_, 1, v_a_1504_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v___x_1528_);
v___x_1530_ = v___x_1524_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1528_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_del_object(v___x_1518_);
lean_dec_ref(v_alts_1516_);
lean_dec(v_discr_1515_);
lean_dec_ref(v_resultType_1514_);
lean_dec(v_typeName_1513_);
lean_dec(v_a_1504_);
lean_dec_ref_known(v_c_1285_, 1);
v_a_1547_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1521_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1521_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec_ref_known(v_c_1285_, 1);
lean_dec_ref(v_cases_1502_);
lean_dec_ref(v_info_1284_);
lean_dec(v_x_1283_);
v_a_1557_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1503_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1503_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
case 5:
{
lean_object* v___x_1565_; 
lean_dec_ref(v_info_1284_);
lean_inc_ref(v_c_1285_);
v___x_1565_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_1285_, v_x_1283_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1574_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1568_ = v___x_1565_;
v_isShared_1569_ = v_isSharedCheck_1574_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1565_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1574_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1570_; lean_object* v___x_1572_; 
v___x_1570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1570_, 0, v_c_1285_);
lean_ctor_set(v___x_1570_, 1, v_a_1566_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v___x_1570_);
v___x_1572_ = v___x_1568_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_dec_ref_known(v_c_1285_, 1);
v_a_1575_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1565_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1565_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
case 6:
{
lean_object* v___x_1583_; 
lean_dec_ref(v_info_1284_);
lean_inc_ref(v_c_1285_);
v___x_1583_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_1285_, v_x_1283_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1592_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1586_ = v___x_1583_;
v_isShared_1587_ = v_isSharedCheck_1592_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1583_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1592_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; lean_object* v___x_1590_; 
v___x_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1588_, 0, v_c_1285_);
lean_ctor_set(v___x_1588_, 1, v_a_1584_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1588_);
v___x_1590_ = v___x_1586_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1588_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_dec_ref_known(v_c_1285_, 1);
v_a_1593_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1583_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1583_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
case 8:
{
lean_object* v_fvarId_1601_; lean_object* v_i_1602_; lean_object* v_y_1603_; lean_object* v_k_1604_; uint8_t v___x_1605_; lean_object* v_instr_1606_; uint8_t v___x_1607_; uint8_t v___x_1608_; 
v_fvarId_1601_ = lean_ctor_get(v_c_1285_, 0);
v_i_1602_ = lean_ctor_get(v_c_1285_, 1);
v_y_1603_ = lean_ctor_get(v_c_1285_, 2);
v_k_1604_ = lean_ctor_get(v_c_1285_, 3);
v___x_1605_ = 1;
v_instr_1606_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_1605_, v_c_1285_);
lean_inc(v_x_1283_);
v___x_1607_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_1606_, v_x_1283_);
v___x_1608_ = 1;
if (v___x_1607_ == 0)
{
lean_object* v___x_1609_; 
lean_inc_ref(v_k_1604_);
lean_inc_ref(v_info_1284_);
lean_inc(v_x_1283_);
v___x_1609_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1283_, v_info_1284_, v_k_1604_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1735_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1612_ = v___x_1609_;
v_isShared_1613_ = v_isSharedCheck_1735_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1609_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1735_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___y_1615_; lean_object* v_snd_1621_; uint8_t v___x_1622_; 
v_snd_1621_ = lean_ctor_get(v_a_1610_, 1);
v___x_1622_ = lean_unbox(v_snd_1621_);
if (v___x_1622_ == 0)
{
lean_object* v_fst_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1718_; 
lean_inc(v_snd_1621_);
lean_del_object(v___x_1612_);
v_fst_1623_ = lean_ctor_get(v_a_1610_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v_a_1610_);
if (v_isSharedCheck_1718_ == 0)
{
lean_object* v_unused_1719_; 
v_unused_1719_ = lean_ctor_get(v_a_1610_, 1);
lean_dec(v_unused_1719_);
v___x_1625_ = v_a_1610_;
v_isShared_1626_ = v_isSharedCheck_1718_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_fst_1623_);
lean_dec(v_a_1610_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1718_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; 
lean_inc(v_x_1283_);
v___x_1627_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1606_, v_x_1283_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1709_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1630_ = v___x_1627_;
v_isShared_1631_ = v_isSharedCheck_1709_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1627_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1709_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___y_1633_; lean_object* v___y_1641_; uint8_t v___x_1645_; 
v___x_1645_ = lean_unbox(v_a_1628_);
lean_dec(v_a_1628_);
switch(v___x_1645_)
{
case 0:
{
size_t v___x_1646_; size_t v___x_1647_; uint8_t v___x_1648_; 
lean_del_object(v___x_1630_);
lean_del_object(v___x_1625_);
lean_dec(v_snd_1621_);
lean_dec_ref(v_info_1284_);
lean_dec(v_x_1283_);
v___x_1646_ = lean_ptr_addr(v_k_1604_);
v___x_1647_ = lean_ptr_addr(v_fst_1623_);
v___x_1648_ = lean_usize_dec_eq(v___x_1646_, v___x_1647_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
lean_inc(v_y_1603_);
lean_inc(v_i_1602_);
lean_inc(v_fvarId_1601_);
v_isSharedCheck_1655_ = !lean_is_exclusive(v_c_1285_);
if (v_isSharedCheck_1655_ == 0)
{
lean_object* v_unused_1656_; lean_object* v_unused_1657_; lean_object* v_unused_1658_; lean_object* v_unused_1659_; 
v_unused_1656_ = lean_ctor_get(v_c_1285_, 3);
lean_dec(v_unused_1656_);
v_unused_1657_ = lean_ctor_get(v_c_1285_, 2);
lean_dec(v_unused_1657_);
v_unused_1658_ = lean_ctor_get(v_c_1285_, 1);
lean_dec(v_unused_1658_);
v_unused_1659_ = lean_ctor_get(v_c_1285_, 0);
lean_dec(v_unused_1659_);
v___x_1650_ = v_c_1285_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_dec(v_c_1285_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 3, v_fst_1623_);
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_fvarId_1601_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v_i_1602_);
lean_ctor_set(v_reuseFailAlloc_1654_, 2, v_y_1603_);
lean_ctor_set(v_reuseFailAlloc_1654_, 3, v_fst_1623_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
v___y_1641_ = v___x_1653_;
goto v___jp_1640_;
}
}
}
else
{
lean_dec(v_fst_1623_);
v___y_1641_ = v_c_1285_;
goto v___jp_1640_;
}
}
case 1:
{
lean_object* v___x_1660_; 
lean_del_object(v___x_1630_);
lean_del_object(v___x_1625_);
lean_dec(v_snd_1621_);
v___x_1660_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_1283_, v_info_1284_, v_fst_1623_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec_ref(v_info_1284_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1686_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1663_ = v___x_1660_;
v_isShared_1664_ = v_isSharedCheck_1686_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1660_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1686_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___y_1666_; size_t v___x_1672_; size_t v___x_1673_; uint8_t v___x_1674_; 
v___x_1672_ = lean_ptr_addr(v_k_1604_);
v___x_1673_ = lean_ptr_addr(v_a_1661_);
v___x_1674_ = lean_usize_dec_eq(v___x_1672_, v___x_1673_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
lean_inc(v_y_1603_);
lean_inc(v_i_1602_);
lean_inc(v_fvarId_1601_);
v_isSharedCheck_1681_ = !lean_is_exclusive(v_c_1285_);
if (v_isSharedCheck_1681_ == 0)
{
lean_object* v_unused_1682_; lean_object* v_unused_1683_; lean_object* v_unused_1684_; lean_object* v_unused_1685_; 
v_unused_1682_ = lean_ctor_get(v_c_1285_, 3);
lean_dec(v_unused_1682_);
v_unused_1683_ = lean_ctor_get(v_c_1285_, 2);
lean_dec(v_unused_1683_);
v_unused_1684_ = lean_ctor_get(v_c_1285_, 1);
lean_dec(v_unused_1684_);
v_unused_1685_ = lean_ctor_get(v_c_1285_, 0);
lean_dec(v_unused_1685_);
v___x_1676_ = v_c_1285_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_dec(v_c_1285_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 3, v_a_1661_);
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_fvarId_1601_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_i_1602_);
lean_ctor_set(v_reuseFailAlloc_1680_, 2, v_y_1603_);
lean_ctor_set(v_reuseFailAlloc_1680_, 3, v_a_1661_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
v___y_1666_ = v___x_1679_;
goto v___jp_1665_;
}
}
}
else
{
lean_dec(v_a_1661_);
v___y_1666_ = v_c_1285_;
goto v___jp_1665_;
}
v___jp_1665_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1667_ = lean_box(v___x_1608_);
v___x_1668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___y_1666_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 0, v___x_1668_);
v___x_1670_ = v___x_1663_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec_ref_known(v_c_1285_, 4);
v_a_1687_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1660_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1660_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
default: 
{
size_t v___x_1695_; size_t v___x_1696_; uint8_t v___x_1697_; 
lean_dec_ref(v_info_1284_);
lean_dec(v_x_1283_);
v___x_1695_ = lean_ptr_addr(v_k_1604_);
v___x_1696_ = lean_ptr_addr(v_fst_1623_);
v___x_1697_ = lean_usize_dec_eq(v___x_1695_, v___x_1696_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_inc(v_y_1603_);
lean_inc(v_i_1602_);
lean_inc(v_fvarId_1601_);
v_isSharedCheck_1704_ = !lean_is_exclusive(v_c_1285_);
if (v_isSharedCheck_1704_ == 0)
{
lean_object* v_unused_1705_; lean_object* v_unused_1706_; lean_object* v_unused_1707_; lean_object* v_unused_1708_; 
v_unused_1705_ = lean_ctor_get(v_c_1285_, 3);
lean_dec(v_unused_1705_);
v_unused_1706_ = lean_ctor_get(v_c_1285_, 2);
lean_dec(v_unused_1706_);
v_unused_1707_ = lean_ctor_get(v_c_1285_, 1);
lean_dec(v_unused_1707_);
v_unused_1708_ = lean_ctor_get(v_c_1285_, 0);
lean_dec(v_unused_1708_);
v___x_1699_ = v_c_1285_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_dec(v_c_1285_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 3, v_fst_1623_);
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_fvarId_1601_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_i_1602_);
lean_ctor_set(v_reuseFailAlloc_1703_, 2, v_y_1603_);
lean_ctor_set(v_reuseFailAlloc_1703_, 3, v_fst_1623_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
v___y_1633_ = v___x_1702_;
goto v___jp_1632_;
}
}
}
else
{
lean_dec(v_fst_1623_);
v___y_1633_ = v_c_1285_;
goto v___jp_1632_;
}
}
}
v___jp_1632_:
{
lean_object* v___x_1635_; 
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___y_1633_);
v___x_1635_ = v___x_1625_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___y_1633_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_snd_1621_);
v___x_1635_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1637_; 
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 0, v___x_1635_);
v___x_1637_ = v___x_1630_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
v___jp_1640_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1642_ = lean_box(v___x_1608_);
v___x_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___y_1641_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
return v___x_1644_;
}
}
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
lean_del_object(v___x_1625_);
lean_dec(v_fst_1623_);
lean_dec(v_snd_1621_);
lean_dec_ref_known(v_c_1285_, 4);
lean_dec_ref(v_info_1284_);
lean_dec(v_x_1283_);
v_a_1710_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1627_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1627_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
}
else
{
lean_object* v_fst_1720_; size_t v___x_1721_; size_t v___x_1722_; uint8_t v___x_1723_; 
lean_dec_ref(v_instr_1606_);
lean_dec_ref(v_info_1284_);
lean_dec(v_x_1283_);
v_fst_1720_ = lean_ctor_get(v_a_1610_, 0);
lean_inc(v_fst_1720_);
lean_dec(v_a_1610_);
v___x_1721_ = lean_ptr_addr(v_k_1604_);
v___x_1722_ = lean_ptr_addr(v_fst_1720_);
v___x_1723_ = lean_usize_dec_eq(v___x_1721_, v___x_1722_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_inc(v_y_1603_);
lean_inc(v_i_1602_);
lean_inc(v_fvarId_1601_);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_c_1285_);
if (v_isSharedCheck_1730_ == 0)
{
lean_object* v_unused_1731_; lean_object* v_unused_1732_; lean_object* v_unused_1733_; lean_object* v_unused_1734_; 
v_unused_1731_ = lean_ctor_get(v_c_1285_, 3);
lean_dec(v_unused_1731_);
v_unused_1732_ = lean_ctor_get(v_c_1285_, 2);
lean_dec(v_unused_1732_);
v_unused_1733_ = lean_ctor_get(v_c_1285_, 1);
lean_dec(v_unused_1733_);
v_unused_1734_ = lean_ctor_get(v_c_1285_, 0);
lean_dec(v_unused_1734_);
v___x_1725_ = v_c_1285_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_dec(v_c_1285_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 3, v_fst_1720_);
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_fvarId_1601_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_i_1602_);
lean_ctor_set(v_reuseFailAlloc_1729_, 2, v_y_1603_);
lean_ctor_set(v_reuseFailAlloc_1729_, 3, v_fst_1720_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
v___y_1615_ = v___x_1728_;
goto v___jp_1614_;
}
}
}
else
{
lean_dec(v_fst_1720_);
v___y_1615_ = v_c_1285_;
goto v___jp_1614_;
}
}
v___jp_1614_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1619_; 
v___x_1616_ = lean_box(v___x_1608_);
v___x_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___y_1615_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 0, v___x_1617_);
v___x_1619_ = v___x_1612_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
else
{
lean_dec_ref(v_instr_1606_);
lean_dec_ref_known(v_c_1285_, 4);
lean_dec_ref(v_info_1284_);
lean_dec(v_x_1283_);
return v___x_1609_;
}
}
else
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
lean_dec_ref(v_instr_1606_);
lean_dec_ref(v_info_1284_);
lean_dec(v_x_1283_);
v___x_1736_ = lean_box(v___x_1608_);
v___x_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1737_, 0, v_c_1285_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
return v___x_1738_;
}
}
case 9:
{
lean_object* v_fvarId_1739_; lean_object* v_i_1740_; lean_object* v_offset_1741_; lean_object* v_y_1742_; lean_object* v_ty_1743_; lean_object* v_k_1744_; uint8_t v___x_1745_; lean_object* v_instr_1746_; uint8_t v___x_1747_; uint8_t v___x_1748_; 
v_fvarId_1739_ = lean_ctor_get(v_c_1285_, 0);
v_i_1740_ = lean_ctor_get(v_c_1285_, 1);
v_offset_1741_ = lean_ctor_get(v_c_1285_, 2);
v_y_1742_ = lean_ctor_get(v_c_1285_, 3);
v_ty_1743_ = lean_ctor_get(v_c_1285_, 4);
v_k_1744_ = lean_ctor_get(v_c_1285_, 5);
v___x_1745_ = 1;
v_instr_1746_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_1745_, v_c_1285_);
lean_inc(v_x_1283_);
v___x_1747_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_1746_, v_x_1283_);
v___x_1748_ = 1;
if (v___x_1747_ == 0)
{
lean_object* v___x_1749_; 
lean_inc_ref(v_k_1744_);
lean_inc_ref(v_info_1284_);
lean_inc(v_x_1283_);
v___x_1749_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1283_, v_info_1284_, v_k_1744_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1883_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1752_ = v___x_1749_;
v_isShared_1753_ = v_isSharedCheck_1883_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1749_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1883_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___y_1755_; lean_object* v_snd_1761_; uint8_t v___x_1762_; 
v_snd_1761_ = lean_ctor_get(v_a_1750_, 1);
v___x_1762_ = lean_unbox(v_snd_1761_);
if (v___x_1762_ == 0)
{
lean_object* v_fst_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1864_; 
lean_inc(v_snd_1761_);
lean_del_object(v___x_1752_);
v_fst_1763_ = lean_ctor_get(v_a_1750_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_a_1750_);
if (v_isSharedCheck_1864_ == 0)
{
lean_object* v_unused_1865_; 
v_unused_1865_ = lean_ctor_get(v_a_1750_, 1);
lean_dec(v_unused_1865_);
v___x_1765_ = v_a_1750_;
v_isShared_1766_ = v_isSharedCheck_1864_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_fst_1763_);
lean_dec(v_a_1750_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1864_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; 
lean_inc(v_x_1283_);
v___x_1767_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1746_, v_x_1283_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1855_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1770_ = v___x_1767_;
v_isShared_1771_ = v_isSharedCheck_1855_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1767_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1855_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___y_1773_; lean_object* v___y_1781_; uint8_t v___x_1785_; 
v___x_1785_ = lean_unbox(v_a_1768_);
lean_dec(v_a_1768_);
switch(v___x_1785_)
{
case 0:
{
size_t v___x_1786_; size_t v___x_1787_; uint8_t v___x_1788_; 
lean_del_object(v___x_1770_);
lean_del_object(v___x_1765_);
lean_dec(v_snd_1761_);
lean_dec_ref(v_info_1284_);
lean_dec(v_x_1283_);
v___x_1786_ = lean_ptr_addr(v_k_1744_);
v___x_1787_ = lean_ptr_addr(v_fst_1763_);
v___x_1788_ = lean_usize_dec_eq(v___x_1786_, v___x_1787_);
if (v___x_1788_ == 0)
{
lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_inc_ref(v_ty_1743_);
lean_inc(v_y_1742_);
lean_inc(v_offset_1741_);
lean_inc(v_i_1740_);
lean_inc(v_fvarId_1739_);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_c_1285_);
if (v_isSharedCheck_1795_ == 0)
{
lean_object* v_unused_1796_; lean_object* v_unused_1797_; lean_object* v_unused_1798_; lean_object* v_unused_1799_; lean_object* v_unused_1800_; lean_object* v_unused_1801_; 
v_unused_1796_ = lean_ctor_get(v_c_1285_, 5);
lean_dec(v_unused_1796_);
v_unused_1797_ = lean_ctor_get(v_c_1285_, 4);
lean_dec(v_unused_1797_);
v_unused_1798_ = lean_ctor_get(v_c_1285_, 3);
lean_dec(v_unused_1798_);
v_unused_1799_ = lean_ctor_get(v_c_1285_, 2);
lean_dec(v_unused_1799_);
v_unused_1800_ = lean_ctor_get(v_c_1285_, 1);
lean_dec(v_unused_1800_);
v_unused_1801_ = lean_ctor_get(v_c_1285_, 0);
lean_dec(v_unused_1801_);
v___x_1790_ = v_c_1285_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_dec(v_c_1285_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 5, v_fst_1763_);
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_fvarId_1739_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_i_1740_);
lean_ctor_set(v_reuseFailAlloc_1794_, 2, v_offset_1741_);
lean_ctor_set(v_reuseFailAlloc_1794_, 3, v_y_1742_);
lean_ctor_set(v_reuseFailAlloc_1794_, 4, v_ty_1743_);
lean_ctor_set(v_reuseFailAlloc_1794_, 5, v_fst_1763_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
v___y_1781_ = v___x_1793_;
goto v___jp_1780_;
}
}
}
else
{
lean_dec(v_fst_1763_);
v___y_1781_ = v_c_1285_;
goto v___jp_1780_;
}
}
case 1:
{
lean_object* v___x_1802_; 
lean_del_object(v___x_1770_);
lean_del_object(v___x_1765_);
lean_dec(v_snd_1761_);
v___x_1802_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_1283_, v_info_1284_, v_fst_1763_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec_ref(v_info_1284_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1830_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1805_ = v___x_1802_;
v_isShared_1806_ = v_isSharedCheck_1830_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1802_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1830_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___y_1808_; size_t v___x_1814_; size_t v___x_1815_; uint8_t v___x_1816_; 
v___x_1814_ = lean_ptr_addr(v_k_1744_);
v___x_1815_ = lean_ptr_addr(v_a_1803_);
v___x_1816_ = lean_usize_dec_eq(v___x_1814_, v___x_1815_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
lean_inc_ref(v_ty_1743_);
lean_inc(v_y_1742_);
lean_inc(v_offset_1741_);
lean_inc(v_i_1740_);
lean_inc(v_fvarId_1739_);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_c_1285_);
if (v_isSharedCheck_1823_ == 0)
{
lean_object* v_unused_1824_; lean_object* v_unused_1825_; lean_object* v_unused_1826_; lean_object* v_unused_1827_; lean_object* v_unused_1828_; lean_object* v_unused_1829_; 
v_unused_1824_ = lean_ctor_get(v_c_1285_, 5);
lean_dec(v_unused_1824_);
v_unused_1825_ = lean_ctor_get(v_c_1285_, 4);
lean_dec(v_unused_1825_);
v_unused_1826_ = lean_ctor_get(v_c_1285_, 3);
lean_dec(v_unused_1826_);
v_unused_1827_ = lean_ctor_get(v_c_1285_, 2);
lean_dec(v_unused_1827_);
v_unused_1828_ = lean_ctor_get(v_c_1285_, 1);
lean_dec(v_unused_1828_);
v_unused_1829_ = lean_ctor_get(v_c_1285_, 0);
lean_dec(v_unused_1829_);
v___x_1818_ = v_c_1285_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_dec(v_c_1285_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 5, v_a_1803_);
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_fvarId_1739_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v_i_1740_);
lean_ctor_set(v_reuseFailAlloc_1822_, 2, v_offset_1741_);
lean_ctor_set(v_reuseFailAlloc_1822_, 3, v_y_1742_);
lean_ctor_set(v_reuseFailAlloc_1822_, 4, v_ty_1743_);
lean_ctor_set(v_reuseFailAlloc_1822_, 5, v_a_1803_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
v___y_1808_ = v___x_1821_;
goto v___jp_1807_;
}
}
}
else
{
lean_dec(v_a_1803_);
v___y_1808_ = v_c_1285_;
goto v___jp_1807_;
}
v___jp_1807_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1812_; 
v___x_1809_ = lean_box(v___x_1748_);
v___x_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___y_1808_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1810_);
v___x_1812_ = v___x_1805_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1810_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
lean_dec_ref_known(v_c_1285_, 6);
v_a_1831_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1833_ = v___x_1802_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1802_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
default: 
{
size_t v___x_1839_; size_t v___x_1840_; uint8_t v___x_1841_; 
lean_dec_ref(v_info_1284_);
lean_dec(v_x_1283_);
v___x_1839_ = lean_ptr_addr(v_k_1744_);
v___x_1840_ = lean_ptr_addr(v_fst_1763_);
v___x_1841_ = lean_usize_dec_eq(v___x_1839_, v___x_1840_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
lean_inc_ref(v_ty_1743_);
lean_inc(v_y_1742_);
lean_inc(v_offset_1741_);
lean_inc(v_i_1740_);
lean_inc(v_fvarId_1739_);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_c_1285_);
if (v_isSharedCheck_1848_ == 0)
{
lean_object* v_unused_1849_; lean_object* v_unused_1850_; lean_object* v_unused_1851_; lean_object* v_unused_1852_; lean_object* v_unused_1853_; lean_object* v_unused_1854_; 
v_unused_1849_ = lean_ctor_get(v_c_1285_, 5);
lean_dec(v_unused_1849_);
v_unused_1850_ = lean_ctor_get(v_c_1285_, 4);
lean_dec(v_unused_1850_);
v_unused_1851_ = lean_ctor_get(v_c_1285_, 3);
lean_dec(v_unused_1851_);
v_unused_1852_ = lean_ctor_get(v_c_1285_, 2);
lean_dec(v_unused_1852_);
v_unused_1853_ = lean_ctor_get(v_c_1285_, 1);
lean_dec(v_unused_1853_);
v_unused_1854_ = lean_ctor_get(v_c_1285_, 0);
lean_dec(v_unused_1854_);
v___x_1843_ = v_c_1285_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_dec(v_c_1285_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 5, v_fst_1763_);
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_fvarId_1739_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_i_1740_);
lean_ctor_set(v_reuseFailAlloc_1847_, 2, v_offset_1741_);
lean_ctor_set(v_reuseFailAlloc_1847_, 3, v_y_1742_);
lean_ctor_set(v_reuseFailAlloc_1847_, 4, v_ty_1743_);
lean_ctor_set(v_reuseFailAlloc_1847_, 5, v_fst_1763_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
v___y_1773_ = v___x_1846_;
goto v___jp_1772_;
}
}
}
else
{
lean_dec(v_fst_1763_);
v___y_1773_ = v_c_1285_;
goto v___jp_1772_;
}
}
}
v___jp_1772_:
{
lean_object* v___x_1775_; 
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___y_1773_);
v___x_1775_ = v___x_1765_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___y_1773_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_snd_1761_);
v___x_1775_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1777_; 
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v___x_1775_);
v___x_1777_ = v___x_1770_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
v___jp_1780_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1782_ = lean_box(v___x_1748_);
v___x_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___y_1781_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
v___x_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
return v___x_1784_;
}
}
}
else
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
lean_del_object(v___x_1765_);
lean_dec(v_fst_1763_);
lean_dec(v_snd_1761_);
lean_dec_ref_known(v_c_1285_, 6);
lean_dec_ref(v_info_1284_);
lean_dec(v_x_1283_);
v_a_1856_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1858_ = v___x_1767_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1767_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
}
else
{
lean_object* v_fst_1866_; size_t v___x_1867_; size_t v___x_1868_; uint8_t v___x_1869_; 
lean_dec_ref(v_instr_1746_);
lean_dec_ref(v_info_1284_);
lean_dec(v_x_1283_);
v_fst_1866_ = lean_ctor_get(v_a_1750_, 0);
lean_inc(v_fst_1866_);
lean_dec(v_a_1750_);
v___x_1867_ = lean_ptr_addr(v_k_1744_);
v___x_1868_ = lean_ptr_addr(v_fst_1866_);
v___x_1869_ = lean_usize_dec_eq(v___x_1867_, v___x_1868_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_inc_ref(v_ty_1743_);
lean_inc(v_y_1742_);
lean_inc(v_offset_1741_);
lean_inc(v_i_1740_);
lean_inc(v_fvarId_1739_);
v_isSharedCheck_1876_ = !lean_is_exclusive(v_c_1285_);
if (v_isSharedCheck_1876_ == 0)
{
lean_object* v_unused_1877_; lean_object* v_unused_1878_; lean_object* v_unused_1879_; lean_object* v_unused_1880_; lean_object* v_unused_1881_; lean_object* v_unused_1882_; 
v_unused_1877_ = lean_ctor_get(v_c_1285_, 5);
lean_dec(v_unused_1877_);
v_unused_1878_ = lean_ctor_get(v_c_1285_, 4);
lean_dec(v_unused_1878_);
v_unused_1879_ = lean_ctor_get(v_c_1285_, 3);
lean_dec(v_unused_1879_);
v_unused_1880_ = lean_ctor_get(v_c_1285_, 2);
lean_dec(v_unused_1880_);
v_unused_1881_ = lean_ctor_get(v_c_1285_, 1);
lean_dec(v_unused_1881_);
v_unused_1882_ = lean_ctor_get(v_c_1285_, 0);
lean_dec(v_unused_1882_);
v___x_1871_ = v_c_1285_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_dec(v_c_1285_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 5, v_fst_1866_);
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_fvarId_1739_);
lean_ctor_set(v_reuseFailAlloc_1875_, 1, v_i_1740_);
lean_ctor_set(v_reuseFailAlloc_1875_, 2, v_offset_1741_);
lean_ctor_set(v_reuseFailAlloc_1875_, 3, v_y_1742_);
lean_ctor_set(v_reuseFailAlloc_1875_, 4, v_ty_1743_);
lean_ctor_set(v_reuseFailAlloc_1875_, 5, v_fst_1866_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
v___y_1755_ = v___x_1874_;
goto v___jp_1754_;
}
}
}
else
{
lean_dec(v_fst_1866_);
v___y_1755_ = v_c_1285_;
goto v___jp_1754_;
}
}
v___jp_1754_:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1759_; 
v___x_1756_ = lean_box(v___x_1748_);
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___y_1755_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1757_);
v___x_1759_ = v___x_1752_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1757_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
else
{
lean_dec_ref(v_instr_1746_);
lean_dec_ref_known(v_c_1285_, 6);
lean_dec_ref(v_info_1284_);
lean_dec(v_x_1283_);
return v___x_1749_;
}
}
else
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_dec_ref(v_instr_1746_);
lean_dec_ref(v_info_1284_);
lean_dec(v_x_1283_);
v___x_1884_ = lean_box(v___x_1748_);
v___x_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1885_, 0, v_c_1285_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
v___x_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
return v___x_1886_;
}
}
default: 
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
lean_dec_ref(v_c_1285_);
lean_dec_ref(v_info_1284_);
lean_dec(v_x_1283_);
v___x_1887_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1);
v___x_1888_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(v___x_1887_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
return v___x_1888_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1283_ = stack[0].m_obj;
lean_object* v_info_1284_ = stack[1].m_obj;
lean_object* v_c_1285_ = stack[2].m_obj;
lean_object* v_a_1286_ = stack[3].m_obj;
lean_object* v_a_1287_ = stack[4].m_obj;
lean_object* v_a_1288_ = stack[5].m_obj;
lean_object* v_a_1289_ = stack[6].m_obj;
lean_object* v_a_1290_ = stack[7].m_obj;
lean_object* v_res_1889_;
v_res_1889_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1283_, v_info_1284_, v_c_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
stack->m_obj
 = v_res_1889_;
}
lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(lean_object* v_x_1890_, lean_object* v_info_1891_, lean_object* v_c_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v___x_1899_; 
lean_inc_ref(v_info_1891_);
lean_inc(v_x_1890_);
v___x_1899_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1890_, v_info_1891_, v_c_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1912_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1902_ = v___x_1899_;
v_isShared_1903_ = v_isSharedCheck_1912_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1912_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v_snd_1904_; uint8_t v___x_1905_; 
v_snd_1904_ = lean_ctor_get(v_a_1900_, 1);
v___x_1905_ = lean_unbox(v_snd_1904_);
if (v___x_1905_ == 0)
{
lean_object* v_fst_1906_; lean_object* v___x_1907_; 
lean_del_object(v___x_1902_);
v_fst_1906_ = lean_ctor_get(v_a_1900_, 0);
lean_inc(v_fst_1906_);
lean_dec(v_a_1900_);
v___x_1907_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_1890_, v_info_1891_, v_fst_1906_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
lean_dec_ref(v_info_1891_);
return v___x_1907_;
}
else
{
lean_object* v_fst_1908_; lean_object* v___x_1910_; 
lean_dec_ref(v_info_1891_);
lean_dec(v_x_1890_);
v_fst_1908_ = lean_ctor_get(v_a_1900_, 0);
lean_inc(v_fst_1908_);
lean_dec(v_a_1900_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v_fst_1908_);
v___x_1910_ = v___x_1902_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_fst_1908_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec_ref(v_info_1891_);
lean_dec(v_x_1890_);
v_a_1913_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1899_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1899_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1890_ = stack[0].m_obj;
lean_object* v_info_1891_ = stack[1].m_obj;
lean_object* v_c_1892_ = stack[2].m_obj;
lean_object* v_a_1893_ = stack[3].m_obj;
lean_object* v_a_1894_ = stack[4].m_obj;
lean_object* v_a_1895_ = stack[5].m_obj;
lean_object* v_a_1896_ = stack[6].m_obj;
lean_object* v_a_1897_ = stack[7].m_obj;
lean_object* v_res_1921_;
v_res_1921_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(v_x_1890_, v_info_1891_, v_c_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
stack->m_obj
 = v_res_1921_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1___boxed(lean_object* v_x_1922_, lean_object* v_info_1923_, lean_object* v_i_1924_, lean_object* v_as_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(v_x_1922_, v_info_1923_, v_i_1924_, v_as_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec_ref(v___y_1926_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___boxed(lean_object* v_x_1933_, lean_object* v_info_1934_, lean_object* v_c_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1933_, v_info_1934_, v_c_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
lean_dec(v_a_1940_);
lean_dec_ref(v_a_1939_);
lean_dec(v_a_1938_);
lean_dec_ref(v_a_1937_);
lean_dec_ref(v_a_1936_);
return v_res_1942_;
}
}
lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0(uint8_t v_pu_1943_, lean_object* v_alt_1944_, lean_object* v_f_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_alt_1944_, v_f_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
return v___x_1952_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1943_ = stack[0].m_num;
lean_object* v_alt_1944_ = stack[1].m_obj;
lean_object* v_f_1945_ = stack[2].m_obj;
lean_object* v___y_1946_ = stack[3].m_obj;
lean_object* v___y_1947_ = stack[4].m_obj;
lean_object* v___y_1948_ = stack[5].m_obj;
lean_object* v___y_1949_ = stack[6].m_obj;
lean_object* v___y_1950_ = stack[7].m_obj;
lean_object* v_res_1953_;
v_res_1953_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0(v_pu_1943_, v_alt_1944_, v_f_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
stack->m_obj
 = v_res_1953_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___boxed(lean_object* v_pu_1954_, lean_object* v_alt_1955_, lean_object* v_f_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
uint8_t v_pu_boxed_1963_; lean_object* v_res_1964_; 
v_pu_boxed_1963_ = lean_unbox(v_pu_1954_);
v_res_1964_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0(v_pu_boxed_1963_, v_alt_1955_, v_f_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec_ref(v___y_1957_);
return v_res_1964_;
}
}
lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4(lean_object* v_msg_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v_toApplicative_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_2008_; 
v___x_1972_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0);
v___x_1973_ = l_StateRefT_x27_instMonad___redArg(v___x_1972_);
v_toApplicative_1974_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2008_ == 0)
{
lean_object* v_unused_2009_; 
v_unused_2009_ = lean_ctor_get(v___x_1973_, 1);
lean_dec(v_unused_2009_);
v___x_1976_ = v___x_1973_;
v_isShared_1977_ = v_isSharedCheck_2008_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_toApplicative_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_2008_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v_toFunctor_1978_; lean_object* v_toSeq_1979_; lean_object* v_toSeqLeft_1980_; lean_object* v_toSeqRight_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2006_; 
v_toFunctor_1978_ = lean_ctor_get(v_toApplicative_1974_, 0);
v_toSeq_1979_ = lean_ctor_get(v_toApplicative_1974_, 2);
v_toSeqLeft_1980_ = lean_ctor_get(v_toApplicative_1974_, 3);
v_toSeqRight_1981_ = lean_ctor_get(v_toApplicative_1974_, 4);
v_isSharedCheck_2006_ = !lean_is_exclusive(v_toApplicative_1974_);
if (v_isSharedCheck_2006_ == 0)
{
lean_object* v_unused_2007_; 
v_unused_2007_ = lean_ctor_get(v_toApplicative_1974_, 1);
lean_dec(v_unused_2007_);
v___x_1983_ = v_toApplicative_1974_;
v_isShared_1984_ = v_isSharedCheck_2006_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_toSeqRight_1981_);
lean_inc(v_toSeqLeft_1980_);
lean_inc(v_toSeq_1979_);
lean_inc(v_toFunctor_1978_);
lean_dec(v_toApplicative_1974_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2006_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___f_1985_; lean_object* v___f_1986_; lean_object* v___f_1987_; lean_object* v___f_1988_; lean_object* v___x_1989_; lean_object* v___f_1990_; lean_object* v___f_1991_; lean_object* v___f_1992_; lean_object* v___x_1994_; 
v___f_1985_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1));
v___f_1986_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2));
lean_inc_ref(v_toFunctor_1978_);
v___f_1987_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1987_, 0, v_toFunctor_1978_);
v___f_1988_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1988_, 0, v_toFunctor_1978_);
v___x_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___f_1987_);
lean_ctor_set(v___x_1989_, 1, v___f_1988_);
v___f_1990_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1990_, 0, v_toSeqRight_1981_);
v___f_1991_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1991_, 0, v_toSeqLeft_1980_);
v___f_1992_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1992_, 0, v_toSeq_1979_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 4, v___f_1990_);
lean_ctor_set(v___x_1983_, 3, v___f_1991_);
lean_ctor_set(v___x_1983_, 2, v___f_1992_);
lean_ctor_set(v___x_1983_, 1, v___f_1985_);
lean_ctor_set(v___x_1983_, 0, v___x_1989_);
v___x_1994_ = v___x_1983_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v___f_1985_);
lean_ctor_set(v_reuseFailAlloc_2005_, 2, v___f_1992_);
lean_ctor_set(v_reuseFailAlloc_2005_, 3, v___f_1991_);
lean_ctor_set(v_reuseFailAlloc_2005_, 4, v___f_1990_);
v___x_1994_ = v_reuseFailAlloc_2005_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
lean_object* v___x_1996_; 
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 1, v___f_1986_);
lean_ctor_set(v___x_1976_, 0, v___x_1994_);
v___x_1996_ = v___x_1976_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_1994_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v___f_1986_);
v___x_1996_ = v_reuseFailAlloc_2004_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___f_2000_; lean_object* v___f_2001_; lean_object* v___x_5014__overap_2002_; lean_object* v___x_2003_; 
v___x_1997_ = l_StateRefT_x27_instMonad___redArg(v___x_1996_);
v___x_1998_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0);
v___x_1999_ = l_instInhabitedOfMonad___redArg(v___x_1997_, v___x_1998_);
v___f_2000_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2000_, 0, v___x_1999_);
v___f_2001_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2001_, 0, v___f_2000_);
v___x_5014__overap_2002_ = lean_panic_fn_borrowed(v___f_2001_, v_msg_1965_);
lean_dec_ref(v___f_2001_);
lean_inc(v___y_1970_);
lean_inc_ref(v___y_1969_);
lean_inc(v___y_1968_);
lean_inc_ref(v___y_1967_);
lean_inc_ref(v___y_1966_);
v___x_2003_ = lean_apply_6(v___x_5014__overap_2002_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, lean_box(0));
return v___x_2003_;
}
}
}
}
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1965_ = stack[0].m_obj;
lean_object* v___y_1966_ = stack[1].m_obj;
lean_object* v___y_1967_ = stack[2].m_obj;
lean_object* v___y_1968_ = stack[3].m_obj;
lean_object* v___y_1969_ = stack[4].m_obj;
lean_object* v___y_1970_ = stack[5].m_obj;
lean_object* v_res_2010_;
v_res_2010_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4(v_msg_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
stack->m_obj
 = v_res_2010_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4___boxed(lean_object* v_msg_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4(v_msg_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec_ref(v___y_2012_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(lean_object* v_a_2019_, lean_object* v_fallback_2020_, lean_object* v_x_2021_){
_start:
{
if (lean_obj_tag(v_x_2021_) == 0)
{
lean_inc(v_fallback_2020_);
return v_fallback_2020_;
}
else
{
lean_object* v_key_2022_; lean_object* v_value_2023_; lean_object* v_tail_2024_; uint8_t v___x_2025_; 
v_key_2022_ = lean_ctor_get(v_x_2021_, 0);
v_value_2023_ = lean_ctor_get(v_x_2021_, 1);
v_tail_2024_ = lean_ctor_get(v_x_2021_, 2);
v___x_2025_ = l_Lean_instBEqFVarId_beq(v_key_2022_, v_a_2019_);
if (v___x_2025_ == 0)
{
v_x_2021_ = v_tail_2024_;
goto _start;
}
else
{
lean_inc(v_value_2023_);
return v_value_2023_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___boxed(lean_object* v_a_2027_, lean_object* v_fallback_2028_, lean_object* v_x_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(v_a_2027_, v_fallback_2028_, v_x_2029_);
lean_dec(v_x_2029_);
lean_dec(v_fallback_2028_);
lean_dec(v_a_2027_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(lean_object* v_m_2031_, lean_object* v_a_2032_, lean_object* v_fallback_2033_){
_start:
{
lean_object* v_buckets_2034_; lean_object* v___x_2035_; uint64_t v___x_2036_; uint64_t v___x_2037_; uint64_t v___x_2038_; uint64_t v_fold_2039_; uint64_t v___x_2040_; uint64_t v___x_2041_; uint64_t v___x_2042_; size_t v___x_2043_; size_t v___x_2044_; size_t v___x_2045_; size_t v___x_2046_; size_t v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v_buckets_2034_ = lean_ctor_get(v_m_2031_, 1);
v___x_2035_ = lean_array_get_size(v_buckets_2034_);
v___x_2036_ = l_Lean_instHashableFVarId_hash(v_a_2032_);
v___x_2037_ = 32ULL;
v___x_2038_ = lean_uint64_shift_right(v___x_2036_, v___x_2037_);
v_fold_2039_ = lean_uint64_xor(v___x_2036_, v___x_2038_);
v___x_2040_ = 16ULL;
v___x_2041_ = lean_uint64_shift_right(v_fold_2039_, v___x_2040_);
v___x_2042_ = lean_uint64_xor(v_fold_2039_, v___x_2041_);
v___x_2043_ = lean_uint64_to_usize(v___x_2042_);
v___x_2044_ = lean_usize_of_nat(v___x_2035_);
v___x_2045_ = ((size_t)1ULL);
v___x_2046_ = lean_usize_sub(v___x_2044_, v___x_2045_);
v___x_2047_ = lean_usize_land(v___x_2043_, v___x_2046_);
v___x_2048_ = lean_array_uget_borrowed(v_buckets_2034_, v___x_2047_);
v___x_2049_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(v_a_2032_, v_fallback_2033_, v___x_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg___boxed(lean_object* v_m_2050_, lean_object* v_a_2051_, lean_object* v_fallback_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(v_m_2050_, v_a_2051_, v_fallback_2052_);
lean_dec(v_fallback_2052_);
lean_dec(v_a_2051_);
lean_dec_ref(v_m_2050_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9___redArg(lean_object* v_x_2054_, lean_object* v_x_2055_, lean_object* v_x_2056_, lean_object* v_x_2057_){
_start:
{
lean_object* v_ks_2058_; lean_object* v_vs_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2083_; 
v_ks_2058_ = lean_ctor_get(v_x_2054_, 0);
v_vs_2059_ = lean_ctor_get(v_x_2054_, 1);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_x_2054_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2061_ = v_x_2054_;
v_isShared_2062_ = v_isSharedCheck_2083_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_vs_2059_);
lean_inc(v_ks_2058_);
lean_dec(v_x_2054_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2083_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2063_ = lean_array_get_size(v_ks_2058_);
v___x_2064_ = lean_nat_dec_lt(v_x_2055_, v___x_2063_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2068_; 
lean_dec(v_x_2055_);
v___x_2065_ = lean_array_push(v_ks_2058_, v_x_2056_);
v___x_2066_ = lean_array_push(v_vs_2059_, v_x_2057_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 1, v___x_2066_);
lean_ctor_set(v___x_2061_, 0, v___x_2065_);
v___x_2068_ = v___x_2061_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
else
{
lean_object* v_k_x27_2070_; uint8_t v___x_2071_; 
v_k_x27_2070_ = lean_array_fget_borrowed(v_ks_2058_, v_x_2055_);
v___x_2071_ = l_Lean_instBEqFVarId_beq(v_x_2056_, v_k_x27_2070_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2073_; 
if (v_isShared_2062_ == 0)
{
v___x_2073_ = v___x_2061_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_ks_2058_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_vs_2059_);
v___x_2073_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = lean_unsigned_to_nat(1u);
v___x_2075_ = lean_nat_add(v_x_2055_, v___x_2074_);
lean_dec(v_x_2055_);
v_x_2054_ = v___x_2073_;
v_x_2055_ = v___x_2075_;
goto _start;
}
}
else
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2081_; 
v___x_2078_ = lean_array_fset(v_ks_2058_, v_x_2055_, v_x_2056_);
v___x_2079_ = lean_array_fset(v_vs_2059_, v_x_2055_, v_x_2057_);
lean_dec(v_x_2055_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 1, v___x_2079_);
lean_ctor_set(v___x_2061_, 0, v___x_2078_);
v___x_2081_ = v___x_2061_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2078_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v___x_2079_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7___redArg(lean_object* v_n_2084_, lean_object* v_k_2085_, lean_object* v_v_2086_){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = lean_unsigned_to_nat(0u);
v___x_2088_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9___redArg(v_n_2084_, v___x_2087_, v_k_2085_, v_v_2086_);
return v___x_2088_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2089_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(lean_object* v_x_2090_, size_t v_x_2091_, size_t v_x_2092_, lean_object* v_x_2093_, lean_object* v_x_2094_){
_start:
{
if (lean_obj_tag(v_x_2090_) == 0)
{
lean_object* v_es_2095_; size_t v___x_2096_; size_t v___x_2097_; lean_object* v_j_2098_; lean_object* v___x_2099_; uint8_t v___x_2100_; 
v_es_2095_ = lean_ctor_get(v_x_2090_, 0);
v___x_2096_ = ((size_t)31ULL);
v___x_2097_ = lean_usize_land(v_x_2091_, v___x_2096_);
v_j_2098_ = lean_usize_to_nat(v___x_2097_);
v___x_2099_ = lean_array_get_size(v_es_2095_);
v___x_2100_ = lean_nat_dec_lt(v_j_2098_, v___x_2099_);
if (v___x_2100_ == 0)
{
lean_dec(v_j_2098_);
lean_dec(v_x_2094_);
lean_dec(v_x_2093_);
return v_x_2090_;
}
else
{
lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2139_; 
lean_inc_ref(v_es_2095_);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_x_2090_);
if (v_isSharedCheck_2139_ == 0)
{
lean_object* v_unused_2140_; 
v_unused_2140_ = lean_ctor_get(v_x_2090_, 0);
lean_dec(v_unused_2140_);
v___x_2102_ = v_x_2090_;
v_isShared_2103_ = v_isSharedCheck_2139_;
goto v_resetjp_2101_;
}
else
{
lean_dec(v_x_2090_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2139_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v_v_2104_; lean_object* v___x_2105_; lean_object* v_xs_x27_2106_; lean_object* v___y_2108_; 
v_v_2104_ = lean_array_fget(v_es_2095_, v_j_2098_);
v___x_2105_ = lean_box(0);
v_xs_x27_2106_ = lean_array_fset(v_es_2095_, v_j_2098_, v___x_2105_);
switch(lean_obj_tag(v_v_2104_))
{
case 0:
{
lean_object* v_key_2113_; lean_object* v_val_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2124_; 
v_key_2113_ = lean_ctor_get(v_v_2104_, 0);
v_val_2114_ = lean_ctor_get(v_v_2104_, 1);
v_isSharedCheck_2124_ = !lean_is_exclusive(v_v_2104_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2116_ = v_v_2104_;
v_isShared_2117_ = v_isSharedCheck_2124_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_val_2114_);
lean_inc(v_key_2113_);
lean_dec(v_v_2104_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2124_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
uint8_t v___x_2118_; 
v___x_2118_ = l_Lean_instBEqFVarId_beq(v_x_2093_, v_key_2113_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
lean_del_object(v___x_2116_);
v___x_2119_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2113_, v_val_2114_, v_x_2093_, v_x_2094_);
v___x_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
v___y_2108_ = v___x_2120_;
goto v___jp_2107_;
}
else
{
lean_object* v___x_2122_; 
lean_dec(v_val_2114_);
lean_dec(v_key_2113_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 1, v_x_2094_);
lean_ctor_set(v___x_2116_, 0, v_x_2093_);
v___x_2122_ = v___x_2116_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_x_2093_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_x_2094_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
v___y_2108_ = v___x_2122_;
goto v___jp_2107_;
}
}
}
}
case 1:
{
lean_object* v_node_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2137_; 
v_node_2125_ = lean_ctor_get(v_v_2104_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_v_2104_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2127_ = v_v_2104_;
v_isShared_2128_ = v_isSharedCheck_2137_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_node_2125_);
lean_dec(v_v_2104_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2137_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
size_t v___x_2129_; size_t v___x_2130_; size_t v___x_2131_; size_t v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2135_; 
v___x_2129_ = ((size_t)5ULL);
v___x_2130_ = lean_usize_shift_right(v_x_2091_, v___x_2129_);
v___x_2131_ = ((size_t)1ULL);
v___x_2132_ = lean_usize_add(v_x_2092_, v___x_2131_);
v___x_2133_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_node_2125_, v___x_2130_, v___x_2132_, v_x_2093_, v_x_2094_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v___x_2133_);
v___x_2135_ = v___x_2127_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2133_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
v___y_2108_ = v___x_2135_;
goto v___jp_2107_;
}
}
}
default: 
{
lean_object* v___x_2138_; 
v___x_2138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2138_, 0, v_x_2093_);
lean_ctor_set(v___x_2138_, 1, v_x_2094_);
v___y_2108_ = v___x_2138_;
goto v___jp_2107_;
}
}
v___jp_2107_:
{
lean_object* v___x_2109_; lean_object* v___x_2111_; 
v___x_2109_ = lean_array_fset(v_xs_x27_2106_, v_j_2098_, v___y_2108_);
lean_dec(v_j_2098_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2109_);
v___x_2111_ = v___x_2102_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2109_);
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
else
{
lean_object* v_ks_2141_; lean_object* v_vs_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2160_; 
v_ks_2141_ = lean_ctor_get(v_x_2090_, 0);
v_vs_2142_ = lean_ctor_get(v_x_2090_, 1);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_x_2090_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2144_ = v_x_2090_;
v_isShared_2145_ = v_isSharedCheck_2160_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_vs_2142_);
lean_inc(v_ks_2141_);
lean_dec(v_x_2090_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2160_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_ks_2141_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_vs_2142_);
v___x_2147_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
lean_object* v_newNode_2148_; size_t v___x_2149_; uint8_t v___x_2150_; 
v_newNode_2148_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7___redArg(v___x_2147_, v_x_2093_, v_x_2094_);
v___x_2149_ = ((size_t)7ULL);
v___x_2150_ = lean_usize_dec_le(v___x_2149_, v_x_2092_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2151_; lean_object* v___x_2152_; uint8_t v___x_2153_; 
v___x_2151_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2148_);
v___x_2152_ = lean_unsigned_to_nat(4u);
v___x_2153_ = lean_nat_dec_lt(v___x_2151_, v___x_2152_);
lean_dec(v___x_2151_);
if (v___x_2153_ == 0)
{
lean_object* v_ks_2154_; lean_object* v_vs_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v_ks_2154_ = lean_ctor_get(v_newNode_2148_, 0);
lean_inc_ref(v_ks_2154_);
v_vs_2155_ = lean_ctor_get(v_newNode_2148_, 1);
lean_inc_ref(v_vs_2155_);
lean_dec_ref(v_newNode_2148_);
v___x_2156_ = lean_unsigned_to_nat(0u);
v___x_2157_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0);
v___x_2158_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(v_x_2092_, v_ks_2154_, v_vs_2155_, v___x_2156_, v___x_2157_);
lean_dec_ref(v_vs_2155_);
lean_dec_ref(v_ks_2154_);
return v___x_2158_;
}
else
{
return v_newNode_2148_;
}
}
else
{
return v_newNode_2148_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2090_ = stack[0].m_obj;
size_t v_x_2091_ = stack[1].m_num;
size_t v_x_2092_ = stack[2].m_num;
lean_object* v_x_2093_ = stack[3].m_obj;
lean_object* v_x_2094_ = stack[4].m_obj;
lean_object* v_res_2161_;
v_res_2161_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_2090_, v_x_2091_, v_x_2092_, v_x_2093_, v_x_2094_);
stack->m_obj
 = v_res_2161_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(size_t v_depth_2162_, lean_object* v_keys_2163_, lean_object* v_vals_2164_, lean_object* v_i_2165_, lean_object* v_entries_2166_){
_start:
{
lean_object* v___x_2167_; uint8_t v___x_2168_; 
v___x_2167_ = lean_array_get_size(v_keys_2163_);
v___x_2168_ = lean_nat_dec_lt(v_i_2165_, v___x_2167_);
if (v___x_2168_ == 0)
{
lean_dec(v_i_2165_);
return v_entries_2166_;
}
else
{
lean_object* v_k_2169_; lean_object* v_v_2170_; uint64_t v___x_2171_; size_t v_h_2172_; size_t v___x_2173_; lean_object* v___x_2174_; size_t v___x_2175_; size_t v___x_2176_; size_t v___x_2177_; size_t v_h_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v_k_2169_ = lean_array_fget_borrowed(v_keys_2163_, v_i_2165_);
v_v_2170_ = lean_array_fget_borrowed(v_vals_2164_, v_i_2165_);
v___x_2171_ = l_Lean_instHashableFVarId_hash(v_k_2169_);
v_h_2172_ = lean_uint64_to_usize(v___x_2171_);
v___x_2173_ = ((size_t)5ULL);
v___x_2174_ = lean_unsigned_to_nat(1u);
v___x_2175_ = ((size_t)1ULL);
v___x_2176_ = lean_usize_sub(v_depth_2162_, v___x_2175_);
v___x_2177_ = lean_usize_mul(v___x_2173_, v___x_2176_);
v_h_2178_ = lean_usize_shift_right(v_h_2172_, v___x_2177_);
v___x_2179_ = lean_nat_add(v_i_2165_, v___x_2174_);
lean_dec(v_i_2165_);
lean_inc(v_v_2170_);
lean_inc(v_k_2169_);
v___x_2180_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_entries_2166_, v_h_2178_, v_depth_2162_, v_k_2169_, v_v_2170_);
v_i_2165_ = v___x_2179_;
v_entries_2166_ = v___x_2180_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2162_ = stack[0].m_num;
lean_object* v_keys_2163_ = stack[1].m_obj;
lean_object* v_vals_2164_ = stack[2].m_obj;
lean_object* v_i_2165_ = stack[3].m_obj;
lean_object* v_entries_2166_ = stack[4].m_obj;
lean_object* v_res_2182_;
v_res_2182_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(v_depth_2162_, v_keys_2163_, v_vals_2164_, v_i_2165_, v_entries_2166_);
stack->m_obj
 = v_res_2182_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_depth_2183_, lean_object* v_keys_2184_, lean_object* v_vals_2185_, lean_object* v_i_2186_, lean_object* v_entries_2187_){
_start:
{
size_t v_depth_boxed_2188_; lean_object* v_res_2189_; 
v_depth_boxed_2188_ = lean_unbox_usize(v_depth_2183_);
lean_dec(v_depth_2183_);
v_res_2189_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(v_depth_boxed_2188_, v_keys_2184_, v_vals_2185_, v_i_2186_, v_entries_2187_);
lean_dec_ref(v_vals_2185_);
lean_dec_ref(v_keys_2184_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___boxed(lean_object* v_x_2190_, lean_object* v_x_2191_, lean_object* v_x_2192_, lean_object* v_x_2193_, lean_object* v_x_2194_){
_start:
{
size_t v_x_5755__boxed_2195_; size_t v_x_5756__boxed_2196_; lean_object* v_res_2197_; 
v_x_5755__boxed_2195_ = lean_unbox_usize(v_x_2191_);
lean_dec(v_x_2191_);
v_x_5756__boxed_2196_ = lean_unbox_usize(v_x_2192_);
lean_dec(v_x_2192_);
v_res_2197_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_2190_, v_x_5755__boxed_2195_, v_x_5756__boxed_2196_, v_x_2193_, v_x_2194_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(lean_object* v_x_2198_, lean_object* v_x_2199_, lean_object* v_x_2200_){
_start:
{
uint64_t v___x_2201_; size_t v___x_2202_; size_t v___x_2203_; lean_object* v___x_2204_; 
v___x_2201_ = l_Lean_instHashableFVarId_hash(v_x_2199_);
v___x_2202_ = lean_uint64_to_usize(v___x_2201_);
v___x_2203_ = ((size_t)1ULL);
v___x_2204_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_2198_, v___x_2202_, v___x_2203_, v_x_2199_, v_x_2200_);
return v___x_2204_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2205_, lean_object* v_i_2206_, lean_object* v_k_2207_){
_start:
{
lean_object* v___x_2208_; uint8_t v___x_2209_; 
v___x_2208_ = lean_array_get_size(v_keys_2205_);
v___x_2209_ = lean_nat_dec_lt(v_i_2206_, v___x_2208_);
if (v___x_2209_ == 0)
{
lean_dec(v_i_2206_);
return v___x_2209_;
}
else
{
lean_object* v_k_x27_2210_; uint8_t v___x_2211_; 
v_k_x27_2210_ = lean_array_fget_borrowed(v_keys_2205_, v_i_2206_);
v___x_2211_ = l_Lean_instBEqFVarId_beq(v_k_2207_, v_k_x27_2210_);
if (v___x_2211_ == 0)
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = lean_unsigned_to_nat(1u);
v___x_2213_ = lean_nat_add(v_i_2206_, v___x_2212_);
lean_dec(v_i_2206_);
v_i_2206_ = v___x_2213_;
goto _start;
}
else
{
lean_dec(v_i_2206_);
return v___x_2209_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2205_ = stack[0].m_obj;
lean_object* v_i_2206_ = stack[1].m_obj;
lean_object* v_k_2207_ = stack[2].m_obj;
uint8_t v_res_2215_;
v_res_2215_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_keys_2205_, v_i_2206_, v_k_2207_);
stack->m_num = v_res_2215_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2216_, lean_object* v_i_2217_, lean_object* v_k_2218_){
_start:
{
uint8_t v_res_2219_; lean_object* v_r_2220_; 
v_res_2219_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_keys_2216_, v_i_2217_, v_k_2218_);
lean_dec(v_k_2218_);
lean_dec_ref(v_keys_2216_);
v_r_2220_ = lean_box(v_res_2219_);
return v_r_2220_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(lean_object* v_x_2221_, size_t v_x_2222_, lean_object* v_x_2223_){
_start:
{
if (lean_obj_tag(v_x_2221_) == 0)
{
lean_object* v_es_2224_; lean_object* v___x_2225_; size_t v___x_2226_; size_t v___x_2227_; lean_object* v_j_2228_; lean_object* v___x_2229_; 
v_es_2224_ = lean_ctor_get(v_x_2221_, 0);
v___x_2225_ = lean_box(2);
v___x_2226_ = ((size_t)31ULL);
v___x_2227_ = lean_usize_land(v_x_2222_, v___x_2226_);
v_j_2228_ = lean_usize_to_nat(v___x_2227_);
v___x_2229_ = lean_array_get_borrowed(v___x_2225_, v_es_2224_, v_j_2228_);
lean_dec(v_j_2228_);
switch(lean_obj_tag(v___x_2229_))
{
case 0:
{
lean_object* v_key_2230_; uint8_t v___x_2231_; 
v_key_2230_ = lean_ctor_get(v___x_2229_, 0);
v___x_2231_ = l_Lean_instBEqFVarId_beq(v_x_2223_, v_key_2230_);
return v___x_2231_;
}
case 1:
{
lean_object* v_node_2232_; size_t v___x_2233_; size_t v___x_2234_; 
v_node_2232_ = lean_ctor_get(v___x_2229_, 0);
v___x_2233_ = ((size_t)5ULL);
v___x_2234_ = lean_usize_shift_right(v_x_2222_, v___x_2233_);
v_x_2221_ = v_node_2232_;
v_x_2222_ = v___x_2234_;
goto _start;
}
default: 
{
uint8_t v___x_2236_; 
v___x_2236_ = 0;
return v___x_2236_;
}
}
}
else
{
lean_object* v_ks_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; 
v_ks_2237_ = lean_ctor_get(v_x_2221_, 0);
v___x_2238_ = lean_unsigned_to_nat(0u);
v___x_2239_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_ks_2237_, v___x_2238_, v_x_2223_);
return v___x_2239_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2221_ = stack[0].m_obj;
size_t v_x_2222_ = stack[1].m_num;
lean_object* v_x_2223_ = stack[2].m_obj;
uint8_t v_res_2240_;
v_res_2240_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_2221_, v_x_2222_, v_x_2223_);
stack->m_num = v_res_2240_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg___boxed(lean_object* v_x_2241_, lean_object* v_x_2242_, lean_object* v_x_2243_){
_start:
{
size_t v_x_6030__boxed_2244_; uint8_t v_res_2245_; lean_object* v_r_2246_; 
v_x_6030__boxed_2244_ = lean_unbox_usize(v_x_2242_);
lean_dec(v_x_2242_);
v_res_2245_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_2241_, v_x_6030__boxed_2244_, v_x_2243_);
lean_dec(v_x_2243_);
lean_dec_ref(v_x_2241_);
v_r_2246_ = lean_box(v_res_2245_);
return v_r_2246_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(lean_object* v_x_2247_, lean_object* v_x_2248_){
_start:
{
uint64_t v___x_2249_; size_t v___x_2250_; uint8_t v___x_2251_; 
v___x_2249_ = l_Lean_instHashableFVarId_hash(v_x_2248_);
v___x_2250_ = lean_uint64_to_usize(v___x_2249_);
v___x_2251_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_2247_, v___x_2250_, v_x_2248_);
return v___x_2251_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2247_ = stack[0].m_obj;
lean_object* v_x_2248_ = stack[1].m_obj;
uint8_t v_res_2252_;
v_res_2252_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_x_2247_, v_x_2248_);
stack->m_num = v_res_2252_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg___boxed(lean_object* v_x_2253_, lean_object* v_x_2254_){
_start:
{
uint8_t v_res_2255_; lean_object* v_r_2256_; 
v_res_2255_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_x_2253_, v_x_2254_);
lean_dec(v_x_2254_);
lean_dec_ref(v_x_2253_);
v_r_2256_ = lean_box(v_res_2255_);
return v_r_2256_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1(void){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2258_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_2259_ = lean_unsigned_to_nat(59u);
v___x_2260_ = lean_unsigned_to_nat(281u);
v___x_2261_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__0));
v___x_2262_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_2263_ = l_mkPanicMessageWithDecl(v___x_2262_, v___x_2261_, v___x_2260_, v___x_2259_, v___x_2258_);
return v___x_2263_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(lean_object* v_c_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
switch(lean_obj_tag(v_c_2264_))
{
case 0:
{
lean_object* v_decl_2271_; lean_object* v_k_2272_; lean_object* v___x_2273_; 
v_decl_2271_ = lean_ctor_get(v_c_2264_, 0);
v_k_2272_ = lean_ctor_get(v_c_2264_, 1);
lean_inc_ref(v_k_2272_);
v___x_2273_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2272_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2296_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2276_ = v___x_2273_;
v_isShared_2277_ = v_isSharedCheck_2296_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2273_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2296_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
size_t v___x_2278_; size_t v___x_2279_; uint8_t v___x_2280_; 
v___x_2278_ = lean_ptr_addr(v_k_2272_);
v___x_2279_ = lean_ptr_addr(v_a_2274_);
v___x_2280_ = lean_usize_dec_eq(v___x_2278_, v___x_2279_);
if (v___x_2280_ == 0)
{
lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2290_; 
lean_inc_ref(v_decl_2271_);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_c_2264_);
if (v_isSharedCheck_2290_ == 0)
{
lean_object* v_unused_2291_; lean_object* v_unused_2292_; 
v_unused_2291_ = lean_ctor_get(v_c_2264_, 1);
lean_dec(v_unused_2291_);
v_unused_2292_ = lean_ctor_get(v_c_2264_, 0);
lean_dec(v_unused_2292_);
v___x_2282_ = v_c_2264_;
v_isShared_2283_ = v_isSharedCheck_2290_;
goto v_resetjp_2281_;
}
else
{
lean_dec(v_c_2264_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2290_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 1, v_a_2274_);
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_decl_2271_);
lean_ctor_set(v_reuseFailAlloc_2289_, 1, v_a_2274_);
v___x_2285_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
lean_object* v___x_2287_; 
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 0, v___x_2285_);
v___x_2287_ = v___x_2276_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
else
{
lean_object* v___x_2294_; 
lean_dec(v_a_2274_);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 0, v_c_2264_);
v___x_2294_ = v___x_2276_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_c_2264_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_2264_, 2);
return v___x_2273_;
}
}
case 2:
{
lean_object* v_decl_2297_; lean_object* v_k_2298_; lean_object* v_params_2299_; lean_object* v_type_2300_; lean_object* v_value_2301_; uint8_t v___x_2302_; lean_object* v___x_2303_; 
v_decl_2297_ = lean_ctor_get(v_c_2264_, 0);
v_k_2298_ = lean_ctor_get(v_c_2264_, 1);
v_params_2299_ = lean_ctor_get(v_decl_2297_, 2);
v_type_2300_ = lean_ctor_get(v_decl_2297_, 3);
v_value_2301_ = lean_ctor_get(v_decl_2297_, 4);
v___x_2302_ = 1;
lean_inc_ref(v_value_2301_);
v___x_2303_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_value_2301_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2305_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2303_, 1);
lean_inc_ref(v_params_2299_);
lean_inc_ref(v_type_2300_);
lean_inc_ref(v_decl_2297_);
v___x_2305_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_2302_, v_decl_2297_, v_type_2300_, v_params_2299_, v_a_2304_, v_a_2267_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2307_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2305_, 1);
lean_inc_ref(v_k_2298_);
v___x_2307_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2298_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2345_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2310_ = v___x_2307_;
v_isShared_2311_ = v_isSharedCheck_2345_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2307_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2345_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
size_t v___x_2312_; size_t v___x_2313_; uint8_t v___x_2314_; 
v___x_2312_ = lean_ptr_addr(v_k_2298_);
v___x_2313_ = lean_ptr_addr(v_a_2308_);
v___x_2314_ = lean_usize_dec_eq(v___x_2312_, v___x_2313_);
if (v___x_2314_ == 0)
{
lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2324_; 
v_isSharedCheck_2324_ = !lean_is_exclusive(v_c_2264_);
if (v_isSharedCheck_2324_ == 0)
{
lean_object* v_unused_2325_; lean_object* v_unused_2326_; 
v_unused_2325_ = lean_ctor_get(v_c_2264_, 1);
lean_dec(v_unused_2325_);
v_unused_2326_ = lean_ctor_get(v_c_2264_, 0);
lean_dec(v_unused_2326_);
v___x_2316_ = v_c_2264_;
v_isShared_2317_ = v_isSharedCheck_2324_;
goto v_resetjp_2315_;
}
else
{
lean_dec(v_c_2264_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2324_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 1, v_a_2308_);
lean_ctor_set(v___x_2316_, 0, v_a_2306_);
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2306_);
lean_ctor_set(v_reuseFailAlloc_2323_, 1, v_a_2308_);
v___x_2319_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
lean_object* v___x_2321_; 
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 0, v___x_2319_);
v___x_2321_ = v___x_2310_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2319_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
else
{
size_t v___x_2327_; size_t v___x_2328_; uint8_t v___x_2329_; 
v___x_2327_ = lean_ptr_addr(v_decl_2297_);
v___x_2328_ = lean_ptr_addr(v_a_2306_);
v___x_2329_ = lean_usize_dec_eq(v___x_2327_, v___x_2328_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2339_; 
v_isSharedCheck_2339_ = !lean_is_exclusive(v_c_2264_);
if (v_isSharedCheck_2339_ == 0)
{
lean_object* v_unused_2340_; lean_object* v_unused_2341_; 
v_unused_2340_ = lean_ctor_get(v_c_2264_, 1);
lean_dec(v_unused_2340_);
v_unused_2341_ = lean_ctor_get(v_c_2264_, 0);
lean_dec(v_unused_2341_);
v___x_2331_ = v_c_2264_;
v_isShared_2332_ = v_isSharedCheck_2339_;
goto v_resetjp_2330_;
}
else
{
lean_dec(v_c_2264_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2339_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2334_; 
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 1, v_a_2308_);
lean_ctor_set(v___x_2331_, 0, v_a_2306_);
v___x_2334_ = v___x_2331_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2306_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v_a_2308_);
v___x_2334_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
lean_object* v___x_2336_; 
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 0, v___x_2334_);
v___x_2336_ = v___x_2310_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2334_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
}
else
{
lean_object* v___x_2343_; 
lean_dec(v_a_2308_);
lean_dec(v_a_2306_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 0, v_c_2264_);
v___x_2343_ = v___x_2310_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_c_2264_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
}
else
{
lean_dec(v_a_2306_);
lean_dec_ref_known(v_c_2264_, 2);
return v___x_2307_;
}
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_dec_ref_known(v_c_2264_, 2);
v_a_2346_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2305_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2305_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
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
lean_dec_ref_known(v_c_2264_, 2);
return v___x_2303_;
}
}
case 3:
{
lean_object* v___x_2354_; 
v___x_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2354_, 0, v_c_2264_);
return v___x_2354_;
}
case 4:
{
lean_object* v_cases_2355_; lean_object* v_typeName_2356_; lean_object* v_resultType_2357_; lean_object* v_discr_2358_; lean_object* v_alts_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2412_; 
v_cases_2355_ = lean_ctor_get(v_c_2264_, 0);
lean_inc_ref(v_cases_2355_);
v_typeName_2356_ = lean_ctor_get(v_cases_2355_, 0);
v_resultType_2357_ = lean_ctor_get(v_cases_2355_, 1);
v_discr_2358_ = lean_ctor_get(v_cases_2355_, 2);
v_alts_2359_ = lean_ctor_get(v_cases_2355_, 3);
v_isSharedCheck_2412_ = !lean_is_exclusive(v_cases_2355_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2361_ = v_cases_2355_;
v_isShared_2362_ = v_isSharedCheck_2412_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_alts_2359_);
lean_inc(v_discr_2358_);
lean_inc(v_resultType_2357_);
lean_inc(v_typeName_2356_);
lean_dec(v_cases_2355_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2412_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v_alreadyFound_2363_; uint8_t v_relaxedReuse_2364_; lean_object* v_ownedness_2365_; uint8_t v___x_2366_; uint8_t v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; uint8_t v___x_2370_; uint8_t v___x_2371_; uint8_t v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; size_t v_sz_2376_; size_t v___x_2377_; lean_object* v___x_2378_; 
v_alreadyFound_2363_ = lean_ctor_get(v_a_2265_, 0);
v_relaxedReuse_2364_ = lean_ctor_get_uint8(v_a_2265_, sizeof(void*)*2);
v_ownedness_2365_ = lean_ctor_get(v_a_2265_, 1);
v___x_2366_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_alreadyFound_2363_, v_discr_2358_);
v___x_2367_ = 0;
v___x_2368_ = lean_box(v___x_2367_);
v___x_2369_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(v_ownedness_2365_, v_discr_2358_, v___x_2368_);
lean_dec(v___x_2368_);
v___x_2370_ = 1;
v___x_2371_ = lean_unbox(v___x_2369_);
lean_dec(v___x_2369_);
v___x_2372_ = l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_2371_, v___x_2370_);
v___x_2373_ = lean_box(0);
lean_inc_n(v_discr_2358_, 2);
lean_inc_ref(v_alreadyFound_2363_);
v___x_2374_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(v_alreadyFound_2363_, v_discr_2358_, v___x_2373_);
lean_inc_ref(v_ownedness_2365_);
v___x_2375_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2375_, 0, v___x_2374_);
lean_ctor_set(v___x_2375_, 1, v_ownedness_2365_);
lean_ctor_set_uint8(v___x_2375_, sizeof(void*)*2, v_relaxedReuse_2364_);
v_sz_2376_ = lean_array_size(v_alts_2359_);
v___x_2377_ = ((size_t)0ULL);
lean_inc_ref(v_alts_2359_);
v___x_2378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(v___x_2372_, v_discr_2358_, v___x_2366_, v_sz_2376_, v___x_2377_, v_alts_2359_, v___x_2375_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
lean_dec_ref_known(v___x_2375_, 2);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2403_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2381_ = v___x_2378_;
v_isShared_2382_ = v_isSharedCheck_2403_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2378_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2403_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
size_t v___x_2383_; size_t v___x_2384_; uint8_t v___x_2385_; 
v___x_2383_ = lean_ptr_addr(v_alts_2359_);
lean_dec_ref(v_alts_2359_);
v___x_2384_ = lean_ptr_addr(v_a_2379_);
v___x_2385_ = lean_usize_dec_eq(v___x_2383_, v___x_2384_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2398_; 
v_isSharedCheck_2398_ = !lean_is_exclusive(v_c_2264_);
if (v_isSharedCheck_2398_ == 0)
{
lean_object* v_unused_2399_; 
v_unused_2399_ = lean_ctor_get(v_c_2264_, 0);
lean_dec(v_unused_2399_);
v___x_2387_ = v_c_2264_;
v_isShared_2388_ = v_isSharedCheck_2398_;
goto v_resetjp_2386_;
}
else
{
lean_dec(v_c_2264_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2398_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 3, v_a_2379_);
v___x_2390_ = v___x_2361_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_typeName_2356_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_resultType_2357_);
lean_ctor_set(v_reuseFailAlloc_2397_, 2, v_discr_2358_);
lean_ctor_set(v_reuseFailAlloc_2397_, 3, v_a_2379_);
v___x_2390_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
lean_object* v___x_2392_; 
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 0, v___x_2390_);
v___x_2392_ = v___x_2387_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2390_);
v___x_2392_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
lean_object* v___x_2394_; 
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 0, v___x_2392_);
v___x_2394_ = v___x_2381_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2392_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
}
else
{
lean_object* v___x_2401_; 
lean_dec(v_a_2379_);
lean_del_object(v___x_2361_);
lean_dec(v_discr_2358_);
lean_dec_ref(v_resultType_2357_);
lean_dec(v_typeName_2356_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 0, v_c_2264_);
v___x_2401_ = v___x_2381_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_c_2264_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_del_object(v___x_2361_);
lean_dec_ref(v_alts_2359_);
lean_dec(v_discr_2358_);
lean_dec_ref(v_resultType_2357_);
lean_dec(v_typeName_2356_);
lean_dec_ref_known(v_c_2264_, 1);
v_a_2404_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2378_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2378_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
}
case 5:
{
lean_object* v___x_2413_; 
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v_c_2264_);
return v___x_2413_;
}
case 6:
{
lean_object* v___x_2414_; 
v___x_2414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2414_, 0, v_c_2264_);
return v___x_2414_;
}
case 8:
{
lean_object* v_fvarId_2415_; lean_object* v_i_2416_; lean_object* v_y_2417_; lean_object* v_k_2418_; lean_object* v___x_2419_; 
v_fvarId_2415_ = lean_ctor_get(v_c_2264_, 0);
v_i_2416_ = lean_ctor_get(v_c_2264_, 1);
v_y_2417_ = lean_ctor_get(v_c_2264_, 2);
v_k_2418_ = lean_ctor_get(v_c_2264_, 3);
lean_inc_ref(v_k_2418_);
v___x_2419_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2418_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2444_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2422_ = v___x_2419_;
v_isShared_2423_ = v_isSharedCheck_2444_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2419_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2444_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
size_t v___x_2424_; size_t v___x_2425_; uint8_t v___x_2426_; 
v___x_2424_ = lean_ptr_addr(v_k_2418_);
v___x_2425_ = lean_ptr_addr(v_a_2420_);
v___x_2426_ = lean_usize_dec_eq(v___x_2424_, v___x_2425_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2436_; 
lean_inc(v_y_2417_);
lean_inc(v_i_2416_);
lean_inc(v_fvarId_2415_);
v_isSharedCheck_2436_ = !lean_is_exclusive(v_c_2264_);
if (v_isSharedCheck_2436_ == 0)
{
lean_object* v_unused_2437_; lean_object* v_unused_2438_; lean_object* v_unused_2439_; lean_object* v_unused_2440_; 
v_unused_2437_ = lean_ctor_get(v_c_2264_, 3);
lean_dec(v_unused_2437_);
v_unused_2438_ = lean_ctor_get(v_c_2264_, 2);
lean_dec(v_unused_2438_);
v_unused_2439_ = lean_ctor_get(v_c_2264_, 1);
lean_dec(v_unused_2439_);
v_unused_2440_ = lean_ctor_get(v_c_2264_, 0);
lean_dec(v_unused_2440_);
v___x_2428_ = v_c_2264_;
v_isShared_2429_ = v_isSharedCheck_2436_;
goto v_resetjp_2427_;
}
else
{
lean_dec(v_c_2264_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2436_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 3, v_a_2420_);
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_fvarId_2415_);
lean_ctor_set(v_reuseFailAlloc_2435_, 1, v_i_2416_);
lean_ctor_set(v_reuseFailAlloc_2435_, 2, v_y_2417_);
lean_ctor_set(v_reuseFailAlloc_2435_, 3, v_a_2420_);
v___x_2431_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
lean_object* v___x_2433_; 
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2431_);
v___x_2433_ = v___x_2422_;
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
}
else
{
lean_object* v___x_2442_; 
lean_dec(v_a_2420_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v_c_2264_);
v___x_2442_ = v___x_2422_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_c_2264_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_2264_, 4);
return v___x_2419_;
}
}
case 9:
{
lean_object* v_fvarId_2445_; lean_object* v_i_2446_; lean_object* v_offset_2447_; lean_object* v_y_2448_; lean_object* v_ty_2449_; lean_object* v_k_2450_; lean_object* v___x_2451_; 
v_fvarId_2445_ = lean_ctor_get(v_c_2264_, 0);
v_i_2446_ = lean_ctor_get(v_c_2264_, 1);
v_offset_2447_ = lean_ctor_get(v_c_2264_, 2);
v_y_2448_ = lean_ctor_get(v_c_2264_, 3);
v_ty_2449_ = lean_ctor_get(v_c_2264_, 4);
v_k_2450_ = lean_ctor_get(v_c_2264_, 5);
lean_inc_ref(v_k_2450_);
v___x_2451_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2450_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2478_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2454_ = v___x_2451_;
v_isShared_2455_ = v_isSharedCheck_2478_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2451_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2478_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
size_t v___x_2456_; size_t v___x_2457_; uint8_t v___x_2458_; 
v___x_2456_ = lean_ptr_addr(v_k_2450_);
v___x_2457_ = lean_ptr_addr(v_a_2452_);
v___x_2458_ = lean_usize_dec_eq(v___x_2456_, v___x_2457_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2468_; 
lean_inc_ref(v_ty_2449_);
lean_inc(v_y_2448_);
lean_inc(v_offset_2447_);
lean_inc(v_i_2446_);
lean_inc(v_fvarId_2445_);
v_isSharedCheck_2468_ = !lean_is_exclusive(v_c_2264_);
if (v_isSharedCheck_2468_ == 0)
{
lean_object* v_unused_2469_; lean_object* v_unused_2470_; lean_object* v_unused_2471_; lean_object* v_unused_2472_; lean_object* v_unused_2473_; lean_object* v_unused_2474_; 
v_unused_2469_ = lean_ctor_get(v_c_2264_, 5);
lean_dec(v_unused_2469_);
v_unused_2470_ = lean_ctor_get(v_c_2264_, 4);
lean_dec(v_unused_2470_);
v_unused_2471_ = lean_ctor_get(v_c_2264_, 3);
lean_dec(v_unused_2471_);
v_unused_2472_ = lean_ctor_get(v_c_2264_, 2);
lean_dec(v_unused_2472_);
v_unused_2473_ = lean_ctor_get(v_c_2264_, 1);
lean_dec(v_unused_2473_);
v_unused_2474_ = lean_ctor_get(v_c_2264_, 0);
lean_dec(v_unused_2474_);
v___x_2460_ = v_c_2264_;
v_isShared_2461_ = v_isSharedCheck_2468_;
goto v_resetjp_2459_;
}
else
{
lean_dec(v_c_2264_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2468_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 5, v_a_2452_);
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_fvarId_2445_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v_i_2446_);
lean_ctor_set(v_reuseFailAlloc_2467_, 2, v_offset_2447_);
lean_ctor_set(v_reuseFailAlloc_2467_, 3, v_y_2448_);
lean_ctor_set(v_reuseFailAlloc_2467_, 4, v_ty_2449_);
lean_ctor_set(v_reuseFailAlloc_2467_, 5, v_a_2452_);
v___x_2463_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
lean_object* v___x_2465_; 
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 0, v___x_2463_);
v___x_2465_ = v___x_2454_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2463_);
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
else
{
lean_object* v___x_2476_; 
lean_dec(v_a_2452_);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 0, v_c_2264_);
v___x_2476_ = v___x_2454_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_c_2264_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_2264_, 6);
return v___x_2451_;
}
}
default: 
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
lean_dec_ref(v_c_2264_);
v___x_2479_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1);
v___x_2480_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4(v___x_2479_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
return v___x_2480_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2264_ = stack[0].m_obj;
lean_object* v_a_2265_ = stack[1].m_obj;
lean_object* v_a_2266_ = stack[2].m_obj;
lean_object* v_a_2267_ = stack[3].m_obj;
lean_object* v_a_2268_ = stack[4].m_obj;
lean_object* v_a_2269_ = stack[5].m_obj;
lean_object* v_res_2481_;
v_res_2481_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_c_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
stack->m_obj
 = v_res_2481_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___boxed(lean_object* v_c_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_c_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_);
lean_dec(v_a_2487_);
lean_dec_ref(v_a_2486_);
lean_dec(v_a_2485_);
lean_dec_ref(v_a_2484_);
lean_dec_ref(v_a_2483_);
return v_res_2489_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(uint8_t v___x_2490_, lean_object* v_discr_2491_, uint8_t v___x_2492_, size_t v_sz_2493_, size_t v_i_2494_, lean_object* v_bs_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
uint8_t v___x_2502_; 
v___x_2502_ = lean_usize_dec_lt(v_i_2494_, v_sz_2493_);
if (v___x_2502_ == 0)
{
lean_object* v___x_2503_; 
lean_dec(v_discr_2491_);
v___x_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2503_, 0, v_bs_2495_);
return v___x_2503_;
}
else
{
lean_object* v___f_2504_; lean_object* v_v_2505_; lean_object* v___x_2506_; lean_object* v_bs_x27_2507_; lean_object* v_a_2509_; lean_object* v___y_2515_; lean_object* v___x_2525_; 
v___f_2504_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___boxed), 7, 0);
v_v_2505_ = lean_array_uget(v_bs_2495_, v_i_2494_);
v___x_2506_ = lean_unsigned_to_nat(0u);
v_bs_x27_2507_ = lean_array_uset(v_bs_2495_, v_i_2494_, v___x_2506_);
v___x_2525_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_v_2505_, v___f_2504_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
if (lean_obj_tag(v_a_2526_) == 1)
{
lean_object* v_info_2527_; lean_object* v_code_2528_; uint8_t v___y_2530_; uint8_t v___x_2542_; 
v_info_2527_ = lean_ctor_get(v_a_2526_, 0);
v_code_2528_ = lean_ctor_get(v_a_2526_, 1);
v___x_2542_ = l_Lean_Compiler_LCNF_CtorInfo_isScalar(v_info_2527_);
if (v___x_2542_ == 0)
{
v___y_2530_ = v___x_2492_;
goto v___jp_2529_;
}
else
{
v___y_2530_ = v___x_2542_;
goto v___jp_2529_;
}
v___jp_2529_:
{
if (v___y_2530_ == 0)
{
if (v___x_2490_ == 0)
{
lean_object* v___x_2531_; 
lean_inc_ref(v_a_2526_);
lean_dec_ref_known(v___x_2525_, 1);
lean_inc_ref(v_code_2528_);
lean_inc_ref(v_info_2527_);
lean_inc(v_discr_2491_);
v___x_2531_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(v_discr_2491_, v_info_2527_, v_code_2528_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2533_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_a_2532_);
lean_dec_ref_known(v___x_2531_, 1);
v___x_2533_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2526_, v_a_2532_);
v_a_2509_ = v___x_2533_;
goto v___jp_2508_;
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
lean_dec_ref_known(v_a_2526_, 2);
lean_dec_ref(v_bs_x27_2507_);
lean_dec(v_discr_2491_);
v_a_2534_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2531_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2531_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
else
{
v___y_2515_ = v___x_2525_;
goto v___jp_2514_;
}
}
else
{
v___y_2515_ = v___x_2525_;
goto v___jp_2514_;
}
}
}
else
{
v___y_2515_ = v___x_2525_;
goto v___jp_2514_;
}
}
else
{
v___y_2515_ = v___x_2525_;
goto v___jp_2514_;
}
v___jp_2508_:
{
size_t v___x_2510_; size_t v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = ((size_t)1ULL);
v___x_2511_ = lean_usize_add(v_i_2494_, v___x_2510_);
v___x_2512_ = lean_array_uset(v_bs_x27_2507_, v_i_2494_, v_a_2509_);
v_i_2494_ = v___x_2511_;
v_bs_2495_ = v___x_2512_;
goto _start;
}
v___jp_2514_:
{
if (lean_obj_tag(v___y_2515_) == 0)
{
lean_object* v_a_2516_; 
v_a_2516_ = lean_ctor_get(v___y_2515_, 0);
lean_inc(v_a_2516_);
lean_dec_ref_known(v___y_2515_, 1);
v_a_2509_ = v_a_2516_;
goto v___jp_2508_;
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2524_; 
lean_dec_ref(v_bs_x27_2507_);
lean_dec(v_discr_2491_);
v_a_2517_ = lean_ctor_get(v___y_2515_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___y_2515_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2519_ = v___y_2515_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___y_2515_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
if (v_isShared_2520_ == 0)
{
v___x_2522_ = v___x_2519_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_a_2517_);
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
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2490_ = stack[0].m_num;
lean_object* v_discr_2491_ = stack[1].m_obj;
uint8_t v___x_2492_ = stack[2].m_num;
size_t v_sz_2493_ = stack[3].m_num;
size_t v_i_2494_ = stack[4].m_num;
lean_object* v_bs_2495_ = stack[5].m_obj;
lean_object* v___y_2496_ = stack[6].m_obj;
lean_object* v___y_2497_ = stack[7].m_obj;
lean_object* v___y_2498_ = stack[8].m_obj;
lean_object* v___y_2499_ = stack[9].m_obj;
lean_object* v___y_2500_ = stack[10].m_obj;
lean_object* v_res_2543_;
v_res_2543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(v___x_2490_, v_discr_2491_, v___x_2492_, v_sz_2493_, v_i_2494_, v_bs_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
stack->m_obj
 = v_res_2543_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3___boxed(lean_object* v___x_2544_, lean_object* v_discr_2545_, lean_object* v___x_2546_, lean_object* v_sz_2547_, lean_object* v_i_2548_, lean_object* v_bs_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
uint8_t v___x_6155__boxed_2556_; uint8_t v___x_6157__boxed_2557_; size_t v_sz_boxed_2558_; size_t v_i_boxed_2559_; lean_object* v_res_2560_; 
v___x_6155__boxed_2556_ = lean_unbox(v___x_2544_);
v___x_6157__boxed_2557_ = lean_unbox(v___x_2546_);
v_sz_boxed_2558_ = lean_unbox_usize(v_sz_2547_);
lean_dec(v_sz_2547_);
v_i_boxed_2559_ = lean_unbox_usize(v_i_2548_);
lean_dec(v_i_2548_);
v_res_2560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(v___x_6155__boxed_2556_, v_discr_2545_, v___x_6157__boxed_2557_, v_sz_boxed_2558_, v_i_boxed_2559_, v_bs_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec_ref(v___y_2550_);
return v_res_2560_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0(lean_object* v_00_u03b2_2561_, lean_object* v_x_2562_, lean_object* v_x_2563_){
_start:
{
uint8_t v___x_2564_; 
v___x_2564_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_x_2562_, v_x_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2562_ = stack[1].m_obj;
lean_object* v_x_2563_ = stack[2].m_obj;
uint8_t v_res_2565_;
v_res_2565_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0(lean_box(0), v_x_2562_, v_x_2563_);
stack->m_num = v_res_2565_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___boxed(lean_object* v_00_u03b2_2566_, lean_object* v_x_2567_, lean_object* v_x_2568_){
_start:
{
uint8_t v_res_2569_; lean_object* v_r_2570_; 
v_res_2569_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0(v_00_u03b2_2566_, v_x_2567_, v_x_2568_);
lean_dec(v_x_2568_);
lean_dec_ref(v_x_2567_);
v_r_2570_ = lean_box(v_res_2569_);
return v_r_2570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1(lean_object* v_00_u03b2_2571_, lean_object* v_m_2572_, lean_object* v_a_2573_, lean_object* v_fallback_2574_){
_start:
{
lean_object* v___x_2575_; 
v___x_2575_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(v_m_2572_, v_a_2573_, v_fallback_2574_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___boxed(lean_object* v_00_u03b2_2576_, lean_object* v_m_2577_, lean_object* v_a_2578_, lean_object* v_fallback_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1(v_00_u03b2_2576_, v_m_2577_, v_a_2578_, v_fallback_2579_);
lean_dec(v_fallback_2579_);
lean_dec(v_a_2578_);
lean_dec_ref(v_m_2577_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2(lean_object* v_00_u03b2_2581_, lean_object* v_x_2582_, lean_object* v_x_2583_, lean_object* v_x_2584_){
_start:
{
lean_object* v___x_2585_; 
v___x_2585_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(v_x_2582_, v_x_2583_, v_x_2584_);
return v___x_2585_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0(lean_object* v_00_u03b2_2586_, lean_object* v_x_2587_, size_t v_x_2588_, lean_object* v_x_2589_){
_start:
{
uint8_t v___x_2590_; 
v___x_2590_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_2587_, v_x_2588_, v_x_2589_);
return v___x_2590_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2587_ = stack[1].m_obj;
size_t v_x_2588_ = stack[2].m_num;
lean_object* v_x_2589_ = stack[3].m_obj;
uint8_t v_res_2591_;
v_res_2591_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0(lean_box(0), v_x_2587_, v_x_2588_, v_x_2589_);
stack->m_num = v_res_2591_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2592_, lean_object* v_x_2593_, lean_object* v_x_2594_, lean_object* v_x_2595_){
_start:
{
size_t v_x_7036__boxed_2596_; uint8_t v_res_2597_; lean_object* v_r_2598_; 
v_x_7036__boxed_2596_ = lean_unbox_usize(v_x_2594_);
lean_dec(v_x_2594_);
v_res_2597_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0(v_00_u03b2_2592_, v_x_2593_, v_x_7036__boxed_2596_, v_x_2595_);
lean_dec(v_x_2595_);
lean_dec_ref(v_x_2593_);
v_r_2598_ = lean_box(v_res_2597_);
return v_r_2598_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2(lean_object* v_00_u03b2_2599_, lean_object* v_a_2600_, lean_object* v_fallback_2601_, lean_object* v_x_2602_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(v_a_2600_, v_fallback_2601_, v_x_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2604_, lean_object* v_a_2605_, lean_object* v_fallback_2606_, lean_object* v_x_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2(v_00_u03b2_2604_, v_a_2605_, v_fallback_2606_, v_x_2607_);
lean_dec(v_x_2607_);
lean_dec(v_fallback_2606_);
lean_dec(v_a_2605_);
return v_res_2608_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4(lean_object* v_00_u03b2_2609_, lean_object* v_x_2610_, size_t v_x_2611_, size_t v_x_2612_, lean_object* v_x_2613_, lean_object* v_x_2614_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_2610_, v_x_2611_, v_x_2612_, v_x_2613_, v_x_2614_);
return v___x_2615_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2610_ = stack[1].m_obj;
size_t v_x_2611_ = stack[2].m_num;
size_t v_x_2612_ = stack[3].m_num;
lean_object* v_x_2613_ = stack[4].m_obj;
lean_object* v_x_2614_ = stack[5].m_obj;
lean_object* v_res_2616_;
v_res_2616_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4(lean_box(0), v_x_2610_, v_x_2611_, v_x_2612_, v_x_2613_, v_x_2614_);
stack->m_obj
 = v_res_2616_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2617_, lean_object* v_x_2618_, lean_object* v_x_2619_, lean_object* v_x_2620_, lean_object* v_x_2621_, lean_object* v_x_2622_){
_start:
{
size_t v_x_7062__boxed_2623_; size_t v_x_7063__boxed_2624_; lean_object* v_res_2625_; 
v_x_7062__boxed_2623_ = lean_unbox_usize(v_x_2619_);
lean_dec(v_x_2619_);
v_x_7063__boxed_2624_ = lean_unbox_usize(v_x_2620_);
lean_dec(v_x_2620_);
v_res_2625_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4(v_00_u03b2_2617_, v_x_2618_, v_x_7062__boxed_2623_, v_x_7063__boxed_2624_, v_x_2621_, v_x_2622_);
return v_res_2625_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2626_, lean_object* v_keys_2627_, lean_object* v_vals_2628_, lean_object* v_heq_2629_, lean_object* v_i_2630_, lean_object* v_k_2631_){
_start:
{
uint8_t v___x_2632_; 
v___x_2632_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_keys_2627_, v_i_2630_, v_k_2631_);
return v___x_2632_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2627_ = stack[1].m_obj;
lean_object* v_vals_2628_ = stack[2].m_obj;
lean_object* v_i_2630_ = stack[4].m_obj;
lean_object* v_k_2631_ = stack[5].m_obj;
uint8_t v_res_2633_;
v_res_2633_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2(lean_box(0), v_keys_2627_, v_vals_2628_, lean_box(0), v_i_2630_, v_k_2631_);
stack->m_num = v_res_2633_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2634_, lean_object* v_keys_2635_, lean_object* v_vals_2636_, lean_object* v_heq_2637_, lean_object* v_i_2638_, lean_object* v_k_2639_){
_start:
{
uint8_t v_res_2640_; lean_object* v_r_2641_; 
v_res_2640_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2(v_00_u03b2_2634_, v_keys_2635_, v_vals_2636_, v_heq_2637_, v_i_2638_, v_k_2639_);
lean_dec(v_k_2639_);
lean_dec_ref(v_vals_2636_);
lean_dec_ref(v_keys_2635_);
v_r_2641_ = lean_box(v_res_2640_);
return v_r_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_2642_, lean_object* v_n_2643_, lean_object* v_k_2644_, lean_object* v_v_2645_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7___redArg(v_n_2643_, v_k_2644_, v_v_2645_);
return v___x_2646_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_2647_, size_t v_depth_2648_, lean_object* v_keys_2649_, lean_object* v_vals_2650_, lean_object* v_heq_2651_, lean_object* v_i_2652_, lean_object* v_entries_2653_){
_start:
{
lean_object* v___x_2654_; 
v___x_2654_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(v_depth_2648_, v_keys_2649_, v_vals_2650_, v_i_2652_, v_entries_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2648_ = stack[1].m_num;
lean_object* v_keys_2649_ = stack[2].m_obj;
lean_object* v_vals_2650_ = stack[3].m_obj;
lean_object* v_i_2652_ = stack[5].m_obj;
lean_object* v_entries_2653_ = stack[6].m_obj;
lean_object* v_res_2655_;
v_res_2655_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8(lean_box(0), v_depth_2648_, v_keys_2649_, v_vals_2650_, lean_box(0), v_i_2652_, v_entries_2653_);
stack->m_obj
 = v_res_2655_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_2656_, lean_object* v_depth_2657_, lean_object* v_keys_2658_, lean_object* v_vals_2659_, lean_object* v_heq_2660_, lean_object* v_i_2661_, lean_object* v_entries_2662_){
_start:
{
size_t v_depth_boxed_2663_; lean_object* v_res_2664_; 
v_depth_boxed_2663_ = lean_unbox_usize(v_depth_2657_);
lean_dec(v_depth_2657_);
v_res_2664_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8(v_00_u03b2_2656_, v_depth_boxed_2663_, v_keys_2658_, v_vals_2659_, v_heq_2660_, v_i_2661_, v_entries_2662_);
lean_dec_ref(v_vals_2659_);
lean_dec_ref(v_keys_2658_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9(lean_object* v_00_u03b2_2665_, lean_object* v_x_2666_, lean_object* v_x_2667_, lean_object* v_x_2668_, lean_object* v_x_2669_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9___redArg(v_x_2666_, v_x_2667_, v_x_2668_, v_x_2669_);
return v___x_2670_;
}
}
lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(lean_object* v_msg_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v_toApplicative_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2744_; 
v___x_2680_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0);
v___x_2681_ = l_StateRefT_x27_instMonad___redArg(v___x_2680_);
v_toApplicative_2682_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2744_ == 0)
{
lean_object* v_unused_2745_; 
v_unused_2745_ = lean_ctor_get(v___x_2681_, 1);
lean_dec(v_unused_2745_);
v___x_2684_ = v___x_2681_;
v_isShared_2685_ = v_isSharedCheck_2744_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_toApplicative_2682_);
lean_dec(v___x_2681_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2744_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v_toFunctor_2686_; lean_object* v_toSeq_2687_; lean_object* v_toSeqLeft_2688_; lean_object* v_toSeqRight_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2742_; 
v_toFunctor_2686_ = lean_ctor_get(v_toApplicative_2682_, 0);
v_toSeq_2687_ = lean_ctor_get(v_toApplicative_2682_, 2);
v_toSeqLeft_2688_ = lean_ctor_get(v_toApplicative_2682_, 3);
v_toSeqRight_2689_ = lean_ctor_get(v_toApplicative_2682_, 4);
v_isSharedCheck_2742_ = !lean_is_exclusive(v_toApplicative_2682_);
if (v_isSharedCheck_2742_ == 0)
{
lean_object* v_unused_2743_; 
v_unused_2743_ = lean_ctor_get(v_toApplicative_2682_, 1);
lean_dec(v_unused_2743_);
v___x_2691_ = v_toApplicative_2682_;
v_isShared_2692_ = v_isSharedCheck_2742_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_toSeqRight_2689_);
lean_inc(v_toSeqLeft_2688_);
lean_inc(v_toSeq_2687_);
lean_inc(v_toFunctor_2686_);
lean_dec(v_toApplicative_2682_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2742_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___f_2693_; lean_object* v___f_2694_; lean_object* v___f_2695_; lean_object* v___f_2696_; lean_object* v___x_2697_; lean_object* v___f_2698_; lean_object* v___f_2699_; lean_object* v___f_2700_; lean_object* v___x_2702_; 
v___f_2693_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1));
v___f_2694_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2));
lean_inc_ref(v_toFunctor_2686_);
v___f_2695_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2695_, 0, v_toFunctor_2686_);
v___f_2696_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2696_, 0, v_toFunctor_2686_);
v___x_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___f_2695_);
lean_ctor_set(v___x_2697_, 1, v___f_2696_);
v___f_2698_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2698_, 0, v_toSeqRight_2689_);
v___f_2699_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2699_, 0, v_toSeqLeft_2688_);
v___f_2700_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2700_, 0, v_toSeq_2687_);
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 4, v___f_2698_);
lean_ctor_set(v___x_2691_, 3, v___f_2699_);
lean_ctor_set(v___x_2691_, 2, v___f_2700_);
lean_ctor_set(v___x_2691_, 1, v___f_2693_);
lean_ctor_set(v___x_2691_, 0, v___x_2697_);
v___x_2702_ = v___x_2691_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2697_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v___f_2693_);
lean_ctor_set(v_reuseFailAlloc_2741_, 2, v___f_2700_);
lean_ctor_set(v_reuseFailAlloc_2741_, 3, v___f_2699_);
lean_ctor_set(v_reuseFailAlloc_2741_, 4, v___f_2698_);
v___x_2702_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
lean_object* v___x_2704_; 
if (v_isShared_2685_ == 0)
{
lean_ctor_set(v___x_2684_, 1, v___f_2694_);
lean_ctor_set(v___x_2684_, 0, v___x_2702_);
v___x_2704_ = v___x_2684_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2702_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v___f_2694_);
v___x_2704_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
lean_object* v___x_2705_; lean_object* v_toApplicative_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2738_; 
v___x_2705_ = l_StateRefT_x27_instMonad___redArg(v___x_2704_);
v_toApplicative_2706_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2738_ == 0)
{
lean_object* v_unused_2739_; 
v_unused_2739_ = lean_ctor_get(v___x_2705_, 1);
lean_dec(v_unused_2739_);
v___x_2708_ = v___x_2705_;
v_isShared_2709_ = v_isSharedCheck_2738_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_toApplicative_2706_);
lean_dec(v___x_2705_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2738_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v_toFunctor_2710_; lean_object* v_toSeq_2711_; lean_object* v_toSeqLeft_2712_; lean_object* v_toSeqRight_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2736_; 
v_toFunctor_2710_ = lean_ctor_get(v_toApplicative_2706_, 0);
v_toSeq_2711_ = lean_ctor_get(v_toApplicative_2706_, 2);
v_toSeqLeft_2712_ = lean_ctor_get(v_toApplicative_2706_, 3);
v_toSeqRight_2713_ = lean_ctor_get(v_toApplicative_2706_, 4);
v_isSharedCheck_2736_ = !lean_is_exclusive(v_toApplicative_2706_);
if (v_isSharedCheck_2736_ == 0)
{
lean_object* v_unused_2737_; 
v_unused_2737_ = lean_ctor_get(v_toApplicative_2706_, 1);
lean_dec(v_unused_2737_);
v___x_2715_ = v_toApplicative_2706_;
v_isShared_2716_ = v_isSharedCheck_2736_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_toSeqRight_2713_);
lean_inc(v_toSeqLeft_2712_);
lean_inc(v_toSeq_2711_);
lean_inc(v_toFunctor_2710_);
lean_dec(v_toApplicative_2706_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2736_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___f_2717_; lean_object* v___f_2718_; lean_object* v___f_2719_; lean_object* v___f_2720_; lean_object* v___x_2721_; lean_object* v___f_2722_; lean_object* v___f_2723_; lean_object* v___f_2724_; lean_object* v___x_2726_; 
v___f_2717_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__0));
v___f_2718_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__1));
lean_inc_ref(v_toFunctor_2710_);
v___f_2719_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2719_, 0, v_toFunctor_2710_);
v___f_2720_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2720_, 0, v_toFunctor_2710_);
v___x_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___f_2719_);
lean_ctor_set(v___x_2721_, 1, v___f_2720_);
v___f_2722_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2722_, 0, v_toSeqRight_2713_);
v___f_2723_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2723_, 0, v_toSeqLeft_2712_);
v___f_2724_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2724_, 0, v_toSeq_2711_);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 4, v___f_2722_);
lean_ctor_set(v___x_2715_, 3, v___f_2723_);
lean_ctor_set(v___x_2715_, 2, v___f_2724_);
lean_ctor_set(v___x_2715_, 1, v___f_2717_);
lean_ctor_set(v___x_2715_, 0, v___x_2721_);
v___x_2726_ = v___x_2715_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2721_);
lean_ctor_set(v_reuseFailAlloc_2735_, 1, v___f_2717_);
lean_ctor_set(v_reuseFailAlloc_2735_, 2, v___f_2724_);
lean_ctor_set(v_reuseFailAlloc_2735_, 3, v___f_2723_);
lean_ctor_set(v_reuseFailAlloc_2735_, 4, v___f_2722_);
v___x_2726_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
lean_object* v___x_2728_; 
if (v_isShared_2709_ == 0)
{
lean_ctor_set(v___x_2708_, 1, v___f_2718_);
lean_ctor_set(v___x_2708_, 0, v___x_2726_);
v___x_2728_ = v___x_2708_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2726_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v___f_2718_);
v___x_2728_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2038__overap_2732_; lean_object* v___x_2733_; 
v___x_2729_ = l_StateRefT_x27_instMonad___redArg(v___x_2728_);
v___x_2730_ = lean_box(0);
v___x_2731_ = l_instInhabitedOfMonad___redArg(v___x_2729_, v___x_2730_);
v___x_2038__overap_2732_ = lean_panic_fn_borrowed(v___x_2731_, v_msg_2673_);
lean_dec(v___x_2731_);
lean_inc(v___y_2678_);
lean_inc_ref(v___y_2677_);
lean_inc(v___y_2676_);
lean_inc_ref(v___y_2675_);
lean_inc(v___y_2674_);
v___x_2733_ = lean_apply_6(v___x_2038__overap_2732_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, lean_box(0));
return v___x_2733_;
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
LEAN_EXPORT void l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2673_ = stack[0].m_obj;
lean_object* v___y_2674_ = stack[1].m_obj;
lean_object* v___y_2675_ = stack[2].m_obj;
lean_object* v___y_2676_ = stack[3].m_obj;
lean_object* v___y_2677_ = stack[4].m_obj;
lean_object* v___y_2678_ = stack[5].m_obj;
lean_object* v_res_2746_;
v_res_2746_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(v_msg_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
stack->m_obj
 = v_res_2746_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___boxed(lean_object* v_msg_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(v_msg_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
return v_res_2754_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1(void){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2756_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_2757_ = lean_unsigned_to_nat(61u);
v___x_2758_ = lean_unsigned_to_nat(304u);
v___x_2759_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__0));
v___x_2760_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_2761_ = l_mkPanicMessageWithDecl(v___x_2760_, v___x_2759_, v___x_2758_, v___x_2757_, v___x_2756_);
return v___x_2761_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(lean_object* v_c_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_){
_start:
{
switch(lean_obj_tag(v_c_2762_))
{
case 0:
{
lean_object* v_decl_2769_; lean_object* v_value_2770_; 
v_decl_2769_ = lean_ctor_get(v_c_2762_, 0);
v_value_2770_ = lean_ctor_get(v_decl_2769_, 3);
if (lean_obj_tag(v_value_2770_) == 11)
{
lean_object* v_k_2771_; lean_object* v_var_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
lean_inc_ref(v_value_2770_);
v_k_2771_ = lean_ctor_get(v_c_2762_, 1);
lean_inc_ref(v_k_2771_);
lean_dec_ref_known(v_c_2762_, 2);
v_var_2772_ = lean_ctor_get(v_value_2770_, 1);
lean_inc(v_var_2772_);
lean_dec_ref_known(v_value_2770_, 2);
v___x_2773_ = lean_st_ref_take(v_a_2763_);
v___x_2774_ = lean_box(0);
v___x_2775_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(v___x_2773_, v_var_2772_, v___x_2774_);
v___x_2776_ = lean_st_ref_put(v_a_2763_, v___x_2775_);
v_c_2762_ = v_k_2771_;
goto _start;
}
else
{
lean_object* v_k_2778_; 
v_k_2778_ = lean_ctor_get(v_c_2762_, 1);
lean_inc_ref(v_k_2778_);
lean_dec_ref_known(v_c_2762_, 2);
v_c_2762_ = v_k_2778_;
goto _start;
}
}
case 2:
{
lean_object* v_decl_2780_; lean_object* v_k_2781_; lean_object* v_value_2782_; lean_object* v___x_2783_; 
v_decl_2780_ = lean_ctor_get(v_c_2762_, 0);
lean_inc_ref(v_decl_2780_);
v_k_2781_ = lean_ctor_get(v_c_2762_, 1);
lean_inc_ref(v_k_2781_);
lean_dec_ref_known(v_c_2762_, 2);
v_value_2782_ = lean_ctor_get(v_decl_2780_, 4);
lean_inc_ref(v_value_2782_);
lean_dec_ref(v_decl_2780_);
v___x_2783_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_value_2782_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_dec_ref_known(v___x_2783_, 1);
v_c_2762_ = v_k_2781_;
goto _start;
}
else
{
lean_dec_ref(v_k_2781_);
return v___x_2783_;
}
}
case 3:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
lean_dec_ref_known(v_c_2762_, 2);
v___x_2785_ = lean_box(0);
v___x_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
return v___x_2786_;
}
case 4:
{
lean_object* v_cases_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2809_; 
v_cases_2787_ = lean_ctor_get(v_c_2762_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v_c_2762_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2789_ = v_c_2762_;
v_isShared_2790_ = v_isSharedCheck_2809_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_cases_2787_);
lean_dec(v_c_2762_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2809_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v_alts_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; uint8_t v___x_2795_; 
v_alts_2791_ = lean_ctor_get(v_cases_2787_, 3);
lean_inc_ref(v_alts_2791_);
lean_dec_ref(v_cases_2787_);
v___x_2792_ = lean_unsigned_to_nat(0u);
v___x_2793_ = lean_array_get_size(v_alts_2791_);
v___x_2794_ = lean_box(0);
v___x_2795_ = lean_nat_dec_lt(v___x_2792_, v___x_2793_);
if (v___x_2795_ == 0)
{
lean_object* v___x_2797_; 
lean_dec_ref(v_alts_2791_);
if (v_isShared_2790_ == 0)
{
lean_ctor_set_tag(v___x_2789_, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2794_);
v___x_2797_ = v___x_2789_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2794_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
else
{
uint8_t v___x_2799_; 
v___x_2799_ = lean_nat_dec_le(v___x_2793_, v___x_2793_);
if (v___x_2799_ == 0)
{
if (v___x_2795_ == 0)
{
lean_object* v___x_2801_; 
lean_dec_ref(v_alts_2791_);
if (v_isShared_2790_ == 0)
{
lean_ctor_set_tag(v___x_2789_, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2794_);
v___x_2801_ = v___x_2789_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2794_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
else
{
size_t v___x_2803_; size_t v___x_2804_; lean_object* v___x_2805_; 
lean_del_object(v___x_2789_);
v___x_2803_ = ((size_t)0ULL);
v___x_2804_ = lean_usize_of_nat(v___x_2793_);
v___x_2805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_alts_2791_, v___x_2803_, v___x_2804_, v___x_2794_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_);
lean_dec_ref(v_alts_2791_);
return v___x_2805_;
}
}
else
{
size_t v___x_2806_; size_t v___x_2807_; lean_object* v___x_2808_; 
lean_del_object(v___x_2789_);
v___x_2806_ = ((size_t)0ULL);
v___x_2807_ = lean_usize_of_nat(v___x_2793_);
v___x_2808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_alts_2791_, v___x_2806_, v___x_2807_, v___x_2794_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_);
lean_dec_ref(v_alts_2791_);
return v___x_2808_;
}
}
}
}
case 5:
{
lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2817_; 
v_isSharedCheck_2817_ = !lean_is_exclusive(v_c_2762_);
if (v_isSharedCheck_2817_ == 0)
{
lean_object* v_unused_2818_; 
v_unused_2818_ = lean_ctor_get(v_c_2762_, 0);
lean_dec(v_unused_2818_);
v___x_2811_ = v_c_2762_;
v_isShared_2812_ = v_isSharedCheck_2817_;
goto v_resetjp_2810_;
}
else
{
lean_dec(v_c_2762_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2817_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2813_; lean_object* v___x_2815_; 
v___x_2813_ = lean_box(0);
if (v_isShared_2812_ == 0)
{
lean_ctor_set_tag(v___x_2811_, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2813_);
v___x_2815_ = v___x_2811_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2813_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
case 6:
{
lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2826_; 
v_isSharedCheck_2826_ = !lean_is_exclusive(v_c_2762_);
if (v_isSharedCheck_2826_ == 0)
{
lean_object* v_unused_2827_; 
v_unused_2827_ = lean_ctor_get(v_c_2762_, 0);
lean_dec(v_unused_2827_);
v___x_2820_ = v_c_2762_;
v_isShared_2821_ = v_isSharedCheck_2826_;
goto v_resetjp_2819_;
}
else
{
lean_dec(v_c_2762_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2826_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2822_; lean_object* v___x_2824_; 
v___x_2822_ = lean_box(0);
if (v_isShared_2821_ == 0)
{
lean_ctor_set_tag(v___x_2820_, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2822_);
v___x_2824_ = v___x_2820_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2822_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
case 8:
{
lean_object* v_k_2828_; 
v_k_2828_ = lean_ctor_get(v_c_2762_, 3);
lean_inc_ref(v_k_2828_);
lean_dec_ref_known(v_c_2762_, 4);
v_c_2762_ = v_k_2828_;
goto _start;
}
case 9:
{
lean_object* v_k_2830_; 
v_k_2830_ = lean_ctor_get(v_c_2762_, 5);
lean_inc_ref(v_k_2830_);
lean_dec_ref_known(v_c_2762_, 6);
v_c_2762_ = v_k_2830_;
goto _start;
}
default: 
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
lean_dec_ref(v_c_2762_);
v___x_2832_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1);
v___x_2833_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(v___x_2832_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_);
return v___x_2833_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2762_ = stack[0].m_obj;
lean_object* v_a_2763_ = stack[1].m_obj;
lean_object* v_a_2764_ = stack[2].m_obj;
lean_object* v_a_2765_ = stack[3].m_obj;
lean_object* v_a_2766_ = stack[4].m_obj;
lean_object* v_a_2767_ = stack[5].m_obj;
lean_object* v_res_2834_;
v_res_2834_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_c_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_);
stack->m_obj
 = v_res_2834_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(lean_object* v_as_2835_, size_t v_i_2836_, size_t v_stop_2837_, lean_object* v_b_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v___y_2846_; uint8_t v___x_2852_; 
v___x_2852_ = lean_usize_dec_eq(v_i_2836_, v_stop_2837_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2853_; 
v___x_2853_ = lean_array_uget_borrowed(v_as_2835_, v_i_2836_);
switch(lean_obj_tag(v___x_2853_))
{
case 0:
{
lean_object* v_code_2854_; 
v_code_2854_ = lean_ctor_get(v___x_2853_, 2);
lean_inc_ref(v_code_2854_);
v___y_2846_ = v_code_2854_;
goto v___jp_2845_;
}
case 1:
{
lean_object* v_code_2855_; 
v_code_2855_ = lean_ctor_get(v___x_2853_, 1);
lean_inc_ref(v_code_2855_);
v___y_2846_ = v_code_2855_;
goto v___jp_2845_;
}
default: 
{
lean_object* v_code_2856_; 
v_code_2856_ = lean_ctor_get(v___x_2853_, 0);
lean_inc_ref(v_code_2856_);
v___y_2846_ = v_code_2856_;
goto v___jp_2845_;
}
}
}
else
{
lean_object* v___x_2857_; 
v___x_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2857_, 0, v_b_2838_);
return v___x_2857_;
}
v___jp_2845_:
{
lean_object* v___x_2847_; 
v___x_2847_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v___y_2846_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2848_; size_t v___x_2849_; size_t v___x_2850_; 
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_a_2848_);
lean_dec_ref_known(v___x_2847_, 1);
v___x_2849_ = ((size_t)1ULL);
v___x_2850_ = lean_usize_add(v_i_2836_, v___x_2849_);
v_i_2836_ = v___x_2850_;
v_b_2838_ = v_a_2848_;
goto _start;
}
else
{
return v___x_2847_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2835_ = stack[0].m_obj;
size_t v_i_2836_ = stack[1].m_num;
size_t v_stop_2837_ = stack[2].m_num;
lean_object* v_b_2838_ = stack[3].m_obj;
lean_object* v___y_2839_ = stack[4].m_obj;
lean_object* v___y_2840_ = stack[5].m_obj;
lean_object* v___y_2841_ = stack[6].m_obj;
lean_object* v___y_2842_ = stack[7].m_obj;
lean_object* v___y_2843_ = stack[8].m_obj;
lean_object* v_res_2858_;
v_res_2858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_as_2835_, v_i_2836_, v_stop_2837_, v_b_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
stack->m_obj
 = v_res_2858_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0___boxed(lean_object* v_as_2859_, lean_object* v_i_2860_, lean_object* v_stop_2861_, lean_object* v_b_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
size_t v_i_boxed_2869_; size_t v_stop_boxed_2870_; lean_object* v_res_2871_; 
v_i_boxed_2869_ = lean_unbox_usize(v_i_2860_);
lean_dec(v_i_2860_);
v_stop_boxed_2870_ = lean_unbox_usize(v_stop_2861_);
lean_dec(v_stop_2861_);
v_res_2871_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_as_2859_, v_i_boxed_2869_, v_stop_boxed_2870_, v_b_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec_ref(v_as_2859_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___boxed(lean_object* v_c_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_c_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
lean_dec(v_a_2877_);
lean_dec_ref(v_a_2876_);
lean_dec(v_a_2875_);
lean_dec_ref(v_a_2874_);
lean_dec(v_a_2873_);
return v_res_2879_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2880_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2881_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__0);
v___x_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
return v___x_2882_;
}
}
lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg(){
_start:
{
lean_object* v___x_2884_; 
v___x_2884_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__1);
return v___x_2884_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2885_;
v_res_2885_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg();
stack->m_obj
 = v_res_2885_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___boxed(lean_object* v___dummy_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg();
return v_res_2887_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2888_; 
v___x_2888_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg();
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0(lean_object* v_00_u03b2_2889_){
_start:
{
lean_object* v___x_2890_; 
v___x_2890_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0);
return v___x_2890_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(lean_object* v_f_2891_, lean_object* v_v_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
if (lean_obj_tag(v_v_2892_) == 0)
{
lean_object* v_code_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2923_; 
v_code_2899_ = lean_ctor_get(v_v_2892_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v_v_2892_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2901_ = v_v_2892_;
v_isShared_2902_ = v_isSharedCheck_2923_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_code_2899_);
lean_dec(v_v_2892_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2923_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2903_; 
lean_inc(v___y_2897_);
lean_inc_ref(v___y_2896_);
lean_inc(v___y_2895_);
lean_inc_ref(v___y_2894_);
lean_inc_ref(v___y_2893_);
v___x_2903_ = lean_apply_7(v_f_2891_, v_code_2899_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, lean_box(0));
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2914_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2906_ = v___x_2903_;
v_isShared_2907_ = v_isSharedCheck_2914_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2903_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2914_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 0, v_a_2904_);
v___x_2909_ = v___x_2901_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
lean_object* v___x_2911_; 
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v___x_2909_);
v___x_2911_ = v___x_2906_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2909_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
else
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
lean_del_object(v___x_2901_);
v_a_2915_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___x_2903_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2903_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
}
else
{
lean_object* v___x_2924_; 
lean_dec_ref(v_f_2891_);
v___x_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2924_, 0, v_v_2892_);
return v___x_2924_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2891_ = stack[0].m_obj;
lean_object* v_v_2892_ = stack[1].m_obj;
lean_object* v___y_2893_ = stack[2].m_obj;
lean_object* v___y_2894_ = stack[3].m_obj;
lean_object* v___y_2895_ = stack[4].m_obj;
lean_object* v___y_2896_ = stack[5].m_obj;
lean_object* v___y_2897_ = stack[6].m_obj;
lean_object* v_res_2925_;
v_res_2925_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v_f_2891_, v_v_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
stack->m_obj
 = v_res_2925_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg___boxed(lean_object* v_f_2926_, lean_object* v_v_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v_f_2926_, v_v_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec_ref(v___y_2928_);
return v_res_2934_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1(uint8_t v_pu_2935_, lean_object* v_f_2936_, lean_object* v_v_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v_f_2936_, v_v_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
return v___x_2944_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2935_ = stack[0].m_num;
lean_object* v_f_2936_ = stack[1].m_obj;
lean_object* v_v_2937_ = stack[2].m_obj;
lean_object* v___y_2938_ = stack[3].m_obj;
lean_object* v___y_2939_ = stack[4].m_obj;
lean_object* v___y_2940_ = stack[5].m_obj;
lean_object* v___y_2941_ = stack[6].m_obj;
lean_object* v___y_2942_ = stack[7].m_obj;
lean_object* v_res_2945_;
v_res_2945_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1(v_pu_2935_, v_f_2936_, v_v_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
stack->m_obj
 = v_res_2945_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___boxed(lean_object* v_pu_2946_, lean_object* v_f_2947_, lean_object* v_v_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
uint8_t v_pu_boxed_2955_; lean_object* v_res_2956_; 
v_pu_boxed_2955_ = lean_unbox(v_pu_2946_);
v_res_2956_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1(v_pu_boxed_2955_, v_f_2947_, v_v_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec_ref(v___y_2949_);
return v_res_2956_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0(lean_object* v_code_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v_alreadyFound_2965_; uint8_t v_relaxedReuse_2966_; lean_object* v_ownedness_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; uint8_t v_relaxedReuse_2974_; 
v_relaxedReuse_2974_ = lean_ctor_get_uint8(v___y_2958_, sizeof(void*)*2);
if (v_relaxedReuse_2974_ == 0)
{
lean_object* v_ownedness_2975_; lean_object* v___x_2976_; 
v_ownedness_2975_ = lean_ctor_get(v___y_2958_, 1);
v___x_2976_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0);
v_alreadyFound_2965_ = v___x_2976_;
v_relaxedReuse_2966_ = v_relaxedReuse_2974_;
v_ownedness_2967_ = v_ownedness_2975_;
v___y_2968_ = v___y_2959_;
v___y_2969_ = v___y_2960_;
v___y_2970_ = v___y_2961_;
v___y_2971_ = v___y_2962_;
goto v___jp_2964_;
}
else
{
lean_object* v_ownedness_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v_ownedness_2977_ = lean_ctor_get(v___y_2958_, 1);
v___x_2978_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0);
v___x_2979_ = lean_st_mk_ref(v___x_2978_);
lean_inc_ref(v_code_2957_);
v___x_2980_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_code_2957_, v___x_2979_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v___x_2981_; 
lean_dec_ref_known(v___x_2980_, 1);
v___x_2981_ = lean_st_ref_get(v___x_2979_);
lean_dec(v___x_2979_);
v_alreadyFound_2965_ = v___x_2981_;
v_relaxedReuse_2966_ = v_relaxedReuse_2974_;
v_ownedness_2967_ = v_ownedness_2977_;
v___y_2968_ = v___y_2959_;
v___y_2969_ = v___y_2960_;
v___y_2970_ = v___y_2961_;
v___y_2971_ = v___y_2962_;
goto v___jp_2964_;
}
else
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2989_; 
lean_dec(v___x_2979_);
lean_dec_ref(v_code_2957_);
v_a_2982_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2984_ = v___x_2980_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2980_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2982_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
v___jp_2964_:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
lean_inc_ref(v_ownedness_2967_);
v___x_2972_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2972_, 0, v_alreadyFound_2965_);
lean_ctor_set(v___x_2972_, 1, v_ownedness_2967_);
lean_ctor_set_uint8(v___x_2972_, sizeof(void*)*2, v_relaxedReuse_2966_);
v___x_2973_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_code_2957_, v___x_2972_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
lean_dec_ref_known(v___x_2972_, 2);
return v___x_2973_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_2957_ = stack[0].m_obj;
lean_object* v___y_2958_ = stack[1].m_obj;
lean_object* v___y_2959_ = stack[2].m_obj;
lean_object* v___y_2960_ = stack[3].m_obj;
lean_object* v___y_2961_ = stack[4].m_obj;
lean_object* v___y_2962_ = stack[5].m_obj;
lean_object* v_res_2990_;
v_res_2990_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0(v_code_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
stack->m_obj
 = v_res_2990_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___boxed(lean_object* v_code_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0(v_code_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec_ref(v___y_2992_);
return v_res_2998_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(lean_object* v_decl_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_){
_start:
{
lean_object* v_toSignature_3007_; lean_object* v_value_3008_; uint8_t v_recursive_3009_; lean_object* v_inlineAttr_x3f_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3035_; 
v_toSignature_3007_ = lean_ctor_get(v_decl_3000_, 0);
v_value_3008_ = lean_ctor_get(v_decl_3000_, 1);
v_recursive_3009_ = lean_ctor_get_uint8(v_decl_3000_, sizeof(void*)*3);
v_inlineAttr_x3f_3010_ = lean_ctor_get(v_decl_3000_, 2);
v_isSharedCheck_3035_ = !lean_is_exclusive(v_decl_3000_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3012_ = v_decl_3000_;
v_isShared_3013_ = v_isSharedCheck_3035_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_inlineAttr_x3f_3010_);
lean_inc(v_value_3008_);
lean_inc(v_toSignature_3007_);
lean_dec(v_decl_3000_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3035_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___f_3014_; lean_object* v___x_3015_; 
v___f_3014_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___closed__0));
v___x_3015_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v___f_3014_, v_value_3008_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3026_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3018_ = v___x_3015_;
v_isShared_3019_ = v_isSharedCheck_3026_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_3015_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3026_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 1, v_a_3016_);
v___x_3021_ = v___x_3012_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_toSignature_3007_);
lean_ctor_set(v_reuseFailAlloc_3025_, 1, v_a_3016_);
lean_ctor_set(v_reuseFailAlloc_3025_, 2, v_inlineAttr_x3f_3010_);
lean_ctor_set_uint8(v_reuseFailAlloc_3025_, sizeof(void*)*3, v_recursive_3009_);
v___x_3021_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
lean_object* v___x_3023_; 
if (v_isShared_3019_ == 0)
{
lean_ctor_set(v___x_3018_, 0, v___x_3021_);
v___x_3023_ = v___x_3018_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_3021_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_del_object(v___x_3012_);
lean_dec(v_inlineAttr_x3f_3010_);
lean_dec_ref(v_toSignature_3007_);
v_a_3027_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3015_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3015_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
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
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_3000_ = stack[0].m_obj;
lean_object* v_a_3001_ = stack[1].m_obj;
lean_object* v_a_3002_ = stack[2].m_obj;
lean_object* v_a_3003_ = stack[3].m_obj;
lean_object* v_a_3004_ = stack[4].m_obj;
lean_object* v_a_3005_ = stack[5].m_obj;
lean_object* v_res_3036_;
v_res_3036_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(v_decl_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
stack->m_obj
 = v_res_3036_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___boxed(lean_object* v_decl_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(v_decl_3037_, v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_);
lean_dec(v_a_3042_);
lean_dec_ref(v_a_3041_);
lean_dec(v_a_3040_);
lean_dec_ref(v_a_3039_);
lean_dec_ref(v_a_3038_);
return v_res_3044_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse(lean_object* v_decl_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_){
_start:
{
lean_object* v___x_3051_; 
v___x_3051_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_3046_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3079_; 
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3054_ = v___x_3051_;
v_isShared_3055_ = v_isSharedCheck_3079_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_3051_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3079_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
uint8_t v_resetReuse_3056_; 
v_resetReuse_3056_ = lean_ctor_get_uint8(v_a_3052_, sizeof(void*)*4 + 2);
lean_dec(v_a_3052_);
if (v_resetReuse_3056_ == 0)
{
lean_object* v___x_3058_; 
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 0, v_decl_3045_);
v___x_3058_ = v___x_3054_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_decl_3045_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
else
{
lean_object* v___x_3060_; 
lean_del_object(v___x_3054_);
lean_inc_ref(v_decl_3045_);
v___x_3060_ = l_Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows(v_decl_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v_a_3061_; lean_object* v___x_3062_; 
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
lean_inc_n(v_a_3061_, 2);
lean_dec_ref_known(v___x_3060_, 1);
v___x_3062_ = l_Lean_Compiler_LCNF_Decl_applyOwnedness(v_decl_3045_, v_a_3061_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v_a_3063_; lean_object* v___x_3064_; uint8_t v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
lean_inc(v_a_3063_);
lean_dec_ref_known(v___x_3062_, 1);
v___x_3064_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0);
v___x_3065_ = 0;
lean_inc(v_a_3061_);
v___x_3066_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3066_, 0, v___x_3064_);
lean_ctor_set(v___x_3066_, 1, v_a_3061_);
lean_ctor_set_uint8(v___x_3066_, sizeof(void*)*2, v___x_3065_);
v___x_3067_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(v_a_3063_, v___x_3066_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_);
lean_dec_ref_known(v___x_3066_, 2);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref_known(v___x_3067_, 1);
v___x_3069_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3069_, 0, v___x_3064_);
lean_ctor_set(v___x_3069_, 1, v_a_3061_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*2, v_resetReuse_3056_);
v___x_3070_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(v_a_3068_, v___x_3069_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_);
lean_dec_ref_known(v___x_3069_, 2);
return v___x_3070_;
}
else
{
lean_dec(v_a_3061_);
return v___x_3067_;
}
}
else
{
lean_dec(v_a_3061_);
return v___x_3062_;
}
}
else
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
lean_dec_ref(v_decl_3045_);
v_a_3071_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3073_ = v___x_3060_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_3060_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
if (v_isShared_3074_ == 0)
{
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
}
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_dec_ref(v_decl_3045_);
v_a_3080_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3051_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3051_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_3045_ = stack[0].m_obj;
lean_object* v_a_3046_ = stack[1].m_obj;
lean_object* v_a_3047_ = stack[2].m_obj;
lean_object* v_a_3048_ = stack[3].m_obj;
lean_object* v_a_3049_ = stack[4].m_obj;
lean_object* v_res_3088_;
v_res_3088_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse(v_decl_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_);
stack->m_obj
 = v_res_3088_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse___boxed(lean_object* v_decl_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse(v_decl_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
lean_dec(v_a_3093_);
lean_dec_ref(v_a_3092_);
lean_dec(v_a_3091_);
lean_dec_ref(v_a_3090_);
return v_res_3095_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_insertResetReuse___closed__3(void){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; uint8_t v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3100_ = lean_unsigned_to_nat(0u);
v___x_3101_ = ((lean_object*)(l_Lean_Compiler_LCNF_insertResetReuse___closed__2));
v___x_3102_ = 2;
v___x_3103_ = ((lean_object*)(l_Lean_Compiler_LCNF_insertResetReuse___closed__1));
v___x_3104_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_3103_, v___x_3102_, v___x_3101_, v___x_3100_);
return v___x_3104_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_insertResetReuse(void){
_start:
{
lean_object* v___x_3105_; 
v___x_3105_ = lean_obj_once(&l_Lean_Compiler_LCNF_insertResetReuse___closed__3, &l_Lean_Compiler_LCNF_insertResetReuse___closed__3_once, _init_l_Lean_Compiler_LCNF_insertResetReuse___closed__3);
return v___x_3105_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3161_ = lean_unsigned_to_nat(2506150707u);
v___x_3162_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3163_ = l_Lean_Name_num___override(v___x_3162_, v___x_3161_);
return v___x_3163_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3165_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3166_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3167_ = l_Lean_Name_str___override(v___x_3166_, v___x_3165_);
return v___x_3167_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3169_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3170_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3171_ = l_Lean_Name_str___override(v___x_3170_, v___x_3169_);
return v___x_3171_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3172_ = lean_unsigned_to_nat(2u);
v___x_3173_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3174_ = l_Lean_Name_num___override(v___x_3173_, v___x_3172_);
return v___x_3174_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3176_; uint8_t v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3176_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3177_ = 1;
v___x_3178_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3179_ = l_Lean_registerTraceClass(v___x_3176_, v___x_3177_, v___x_3178_);
return v___x_3179_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3180_;
v_res_3180_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3180_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2____boxed(lean_object* v_a_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_();
return v_res_3182_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_LiveVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PropagateBorrow(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ResetReuse(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_LiveVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_DependsOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PropagateBorrow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_insertResetReuse = _init_l_Lean_Compiler_LCNF_insertResetReuse();
lean_mark_persistent(l_Lean_Compiler_LCNF_insertResetReuse);
res = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ResetReuse(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_LiveVars(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PropagateBorrow(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ResetReuse(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_LiveVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_DependsOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PropagateBorrow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ResetReuse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ResetReuse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ResetReuse(builtin);
}
#ifdef __cplusplus
}
#endif
