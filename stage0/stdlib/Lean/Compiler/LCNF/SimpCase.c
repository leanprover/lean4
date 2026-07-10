// Lean compiler output
// Module: Lean.Compiler.LCNF.SimpCase
// Imports: public import Lean.Compiler.LCNF.CompilerM public import Lean.Compiler.LCNF.PassManager import Lean.Compiler.LCNF.AlphaEqv import Init.Omega
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_alphaEqv(uint8_t, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(uint8_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
size_t lean_ptr_addr(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Compiler.LCNF.SimpCase"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "_private.Lean.Compiler.LCNF.SimpCase.0.Lean.Compiler.LCNF.addDefaultAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureHasDefault(lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_simpCase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpCase"};
static const lean_object* l_Lean_Compiler_LCNF_simpCase___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_simpCase___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_simpCase___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_simpCase___closed__0_value),LEAN_SCALAR_PTR_LITERAL(68, 92, 41, 80, 34, 13, 30, 2)}};
static const lean_object* l_Lean_Compiler_LCNF_simpCase___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_simpCase___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_simpCase___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_simpCase___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_simpCase___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_simpCase___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_simpCase___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simpCase;
static const lean_string_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_simpCase___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 115, 95, 67, 81, 150, 198, 169)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "SimpCase"};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(148, 85, 95, 162, 237, 93, 136, 210)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(149, 85, 1, 1, 249, 114, 201, 242)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(128, 195, 27, 71, 70, 238, 5, 249)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(218, 73, 79, 143, 6, 98, 132, 204)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 66, 31, 97, 69, 225, 237, 3)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(10, 203, 5, 135, 216, 0, 147, 100)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 166, 14, 190, 157, 30, 192, 24)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 200, 250, 209, 136, 24, 111, 216)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 208, 198, 202, 11, 103, 204, 69)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 185, 0, 153, 59, 162, 228, 227)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(136, 14, 40, 21, 139, 206, 91, 108)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1808010913) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(44, 138, 246, 18, 227, 5, 112, 193)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(227, 122, 251, 129, 187, 139, 157, 59)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(131, 16, 117, 131, 59, 32, 143, 15)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(70, 179, 246, 216, 56, 171, 143, 161)}};
static const lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(lean_object* v_upperBound_1_, lean_object* v_alts_2_, lean_object* v_code_3_, lean_object* v_a_4_, lean_object* v_b_5_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = lean_nat_dec_lt(v_a_4_, v_upperBound_1_);
if (v___x_6_ == 0)
{
lean_dec(v_a_4_);
lean_dec_ref(v_code_3_);
return v_b_5_;
}
else
{
uint8_t v___x_7_; lean_object* v_n_8_; lean_object* v_a_10_; lean_object* v___y_14_; lean_object* v___x_17_; 
v___x_7_ = 1;
v_n_8_ = lean_unsigned_to_nat(1u);
v___x_17_ = lean_array_fget_borrowed(v_alts_2_, v_a_4_);
switch(lean_obj_tag(v___x_17_))
{
case 0:
{
lean_object* v_code_18_; 
v_code_18_ = lean_ctor_get(v___x_17_, 2);
lean_inc_ref(v_code_18_);
v___y_14_ = v_code_18_;
goto v___jp_13_;
}
case 1:
{
lean_object* v_code_19_; 
v_code_19_ = lean_ctor_get(v___x_17_, 1);
lean_inc_ref(v_code_19_);
v___y_14_ = v_code_19_;
goto v___jp_13_;
}
default: 
{
lean_object* v_code_20_; 
v_code_20_ = lean_ctor_get(v___x_17_, 0);
lean_inc_ref(v_code_20_);
v___y_14_ = v_code_20_;
goto v___jp_13_;
}
}
v___jp_9_:
{
lean_object* v___x_11_; 
v___x_11_ = lean_nat_add(v_a_4_, v_n_8_);
lean_dec(v_a_4_);
v_a_4_ = v___x_11_;
v_b_5_ = v_a_10_;
goto _start;
}
v___jp_13_:
{
uint8_t v___x_15_; 
lean_inc_ref(v_code_3_);
v___x_15_ = l_Lean_Compiler_LCNF_Code_alphaEqv(v___x_7_, v___y_14_, v_code_3_);
if (v___x_15_ == 0)
{
v_a_10_ = v_b_5_;
goto v___jp_9_;
}
else
{
lean_object* v___x_16_; 
v___x_16_ = lean_nat_add(v_b_5_, v_n_8_);
lean_dec(v_b_5_);
v_a_10_ = v___x_16_;
goto v___jp_9_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg___boxed(lean_object* v_upperBound_21_, lean_object* v_alts_22_, lean_object* v_code_23_, lean_object* v_a_24_, lean_object* v_b_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(v_upperBound_21_, v_alts_22_, v_code_23_, v_a_24_, v_b_25_);
lean_dec_ref(v_alts_22_);
lean_dec(v_upperBound_21_);
return v_res_26_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0(void){
_start:
{
uint8_t v___x_27_; lean_object* v___x_28_; 
v___x_27_ = 1;
v___x_28_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf(lean_object* v_alts_29_, lean_object* v_i_30_){
_start:
{
lean_object* v___x_31_; lean_object* v_n_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_31_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0, &l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0_once, _init_l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0);
v_n_32_ = lean_unsigned_to_nat(1u);
v___x_33_ = lean_nat_add(v_i_30_, v_n_32_);
v___x_34_ = lean_array_get_size(v_alts_29_);
v___x_35_ = lean_array_get_borrowed(v___x_31_, v_alts_29_, v_i_30_);
switch(lean_obj_tag(v___x_35_))
{
case 0:
{
lean_object* v_code_36_; lean_object* v___x_37_; 
v_code_36_ = lean_ctor_get(v___x_35_, 2);
lean_inc_ref(v_code_36_);
v___x_37_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(v___x_34_, v_alts_29_, v_code_36_, v___x_33_, v_n_32_);
return v___x_37_;
}
case 1:
{
lean_object* v_code_38_; lean_object* v___x_39_; 
v_code_38_ = lean_ctor_get(v___x_35_, 1);
lean_inc_ref(v_code_38_);
v___x_39_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(v___x_34_, v_alts_29_, v_code_38_, v___x_33_, v_n_32_);
return v___x_39_;
}
default: 
{
lean_object* v_code_40_; lean_object* v___x_41_; 
v_code_40_ = lean_ctor_get(v___x_35_, 0);
lean_inc_ref(v_code_40_);
v___x_41_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(v___x_34_, v_alts_29_, v_code_40_, v___x_33_, v_n_32_);
return v___x_41_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___boxed(lean_object* v_alts_42_, lean_object* v_i_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf(v_alts_42_, v_i_43_);
lean_dec(v_i_43_);
lean_dec_ref(v_alts_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0(lean_object* v_upperBound_45_, lean_object* v_alts_46_, lean_object* v_code_47_, lean_object* v_inst_48_, lean_object* v_R_49_, lean_object* v_a_50_, lean_object* v_b_51_, lean_object* v_c_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___redArg(v_upperBound_45_, v_alts_46_, v_code_47_, v_a_50_, v_b_51_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0___boxed(lean_object* v_upperBound_54_, lean_object* v_alts_55_, lean_object* v_code_56_, lean_object* v_inst_57_, lean_object* v_R_58_, lean_object* v_a_59_, lean_object* v_b_60_, lean_object* v_c_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf_spec__0(v_upperBound_54_, v_alts_55_, v_code_56_, v_inst_57_, v_R_58_, v_a_59_, v_b_60_, v_c_61_);
lean_dec_ref(v_alts_55_);
lean_dec(v_upperBound_54_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___redArg(lean_object* v_upperBound_63_, lean_object* v_alts_64_, lean_object* v_a_65_, lean_object* v_b_66_){
_start:
{
lean_object* v_a_68_; uint8_t v___x_72_; 
v___x_72_ = lean_nat_dec_lt(v_a_65_, v_upperBound_63_);
if (v___x_72_ == 0)
{
lean_dec(v_a_65_);
return v_b_66_;
}
else
{
lean_object* v_fst_73_; lean_object* v_snd_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_87_; 
v_fst_73_ = lean_ctor_get(v_b_66_, 0);
v_snd_74_ = lean_ctor_get(v_b_66_, 1);
v_isSharedCheck_87_ = !lean_is_exclusive(v_b_66_);
if (v_isSharedCheck_87_ == 0)
{
v___x_76_ = v_b_66_;
v_isShared_77_ = v_isSharedCheck_87_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_snd_74_);
lean_inc(v_fst_73_);
lean_dec(v_b_66_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_87_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf(v_alts_64_, v_a_65_);
v___x_79_ = lean_nat_dec_lt(v_snd_74_, v___x_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_81_; 
lean_dec(v___x_78_);
if (v_isShared_77_ == 0)
{
v___x_81_ = v___x_76_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_fst_73_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v_snd_74_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
v_a_68_ = v___x_81_;
goto v___jp_67_;
}
}
else
{
lean_object* v___x_83_; lean_object* v___x_85_; 
lean_dec(v_snd_74_);
lean_dec(v_fst_73_);
v___x_83_ = lean_array_fget_borrowed(v_alts_64_, v_a_65_);
lean_inc(v___x_83_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 1, v___x_78_);
lean_ctor_set(v___x_76_, 0, v___x_83_);
v___x_85_ = v___x_76_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_83_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v___x_78_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
v_a_68_ = v___x_85_;
goto v___jp_67_;
}
}
}
}
v___jp_67_:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_unsigned_to_nat(1u);
v___x_70_ = lean_nat_add(v_a_65_, v___x_69_);
lean_dec(v_a_65_);
v_a_65_ = v___x_70_;
v_b_66_ = v_a_68_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___redArg___boxed(lean_object* v_upperBound_88_, lean_object* v_alts_89_, lean_object* v_a_90_, lean_object* v_b_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___redArg(v_upperBound_88_, v_alts_89_, v_a_90_, v_b_91_);
lean_dec_ref(v_alts_89_);
lean_dec(v_upperBound_88_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs(lean_object* v_alts_93_){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v_maxAlt_98_; lean_object* v_max_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v_fst_102_; lean_object* v_snd_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_110_; 
v___x_94_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0, &l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0_once, _init_l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0);
v___x_95_ = lean_unsigned_to_nat(1u);
v___x_96_ = lean_array_get_size(v_alts_93_);
v___x_97_ = lean_unsigned_to_nat(0u);
v_maxAlt_98_ = lean_array_get_borrowed(v___x_94_, v_alts_93_, v___x_97_);
v_max_99_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf(v_alts_93_, v___x_97_);
lean_inc(v_maxAlt_98_);
v___x_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_100_, 0, v_maxAlt_98_);
lean_ctor_set(v___x_100_, 1, v_max_99_);
v___x_101_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___redArg(v___x_96_, v_alts_93_, v___x_95_, v___x_100_);
v_fst_102_ = lean_ctor_get(v___x_101_, 0);
v_snd_103_ = lean_ctor_get(v___x_101_, 1);
v_isSharedCheck_110_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_110_ == 0)
{
v___x_105_ = v___x_101_;
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_snd_103_);
lean_inc(v_fst_102_);
lean_dec(v___x_101_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_108_; 
if (v_isShared_106_ == 0)
{
v___x_108_ = v___x_105_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_fst_102_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v_snd_103_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs___boxed(lean_object* v_alts_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs(v_alts_111_);
lean_dec_ref(v_alts_111_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0(lean_object* v_upperBound_113_, lean_object* v_alts_114_, lean_object* v_inst_115_, lean_object* v_R_116_, lean_object* v_a_117_, lean_object* v_b_118_, lean_object* v_c_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___redArg(v_upperBound_113_, v_alts_114_, v_a_117_, v_b_118_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0___boxed(lean_object* v_upperBound_121_, lean_object* v_alts_122_, lean_object* v_inst_123_, lean_object* v_R_124_, lean_object* v_a_125_, lean_object* v_b_126_, lean_object* v_c_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_spec__0(v_upperBound_121_, v_alts_122_, v_inst_123_, v_R_124_, v_a_125_, v_b_126_, v_c_127_);
lean_dec_ref(v_alts_122_);
lean_dec(v_upperBound_121_);
return v_res_128_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__0(void){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_instMonadEIO(lean_box(0));
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0(lean_object* v_msg_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v_toApplicative_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_173_; 
v___x_138_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__0);
v___x_139_ = l_StateRefT_x27_instMonad___redArg(v___x_138_);
v_toApplicative_140_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_173_ == 0)
{
lean_object* v_unused_174_; 
v_unused_174_ = lean_ctor_get(v___x_139_, 1);
lean_dec(v_unused_174_);
v___x_142_ = v___x_139_;
v_isShared_143_ = v_isSharedCheck_173_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_toApplicative_140_);
lean_dec(v___x_139_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_173_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v_toFunctor_144_; lean_object* v_toSeq_145_; lean_object* v_toSeqLeft_146_; lean_object* v_toSeqRight_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_171_; 
v_toFunctor_144_ = lean_ctor_get(v_toApplicative_140_, 0);
v_toSeq_145_ = lean_ctor_get(v_toApplicative_140_, 2);
v_toSeqLeft_146_ = lean_ctor_get(v_toApplicative_140_, 3);
v_toSeqRight_147_ = lean_ctor_get(v_toApplicative_140_, 4);
v_isSharedCheck_171_ = !lean_is_exclusive(v_toApplicative_140_);
if (v_isSharedCheck_171_ == 0)
{
lean_object* v_unused_172_; 
v_unused_172_ = lean_ctor_get(v_toApplicative_140_, 1);
lean_dec(v_unused_172_);
v___x_149_ = v_toApplicative_140_;
v_isShared_150_ = v_isSharedCheck_171_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_toSeqRight_147_);
lean_inc(v_toSeqLeft_146_);
lean_inc(v_toSeq_145_);
lean_inc(v_toFunctor_144_);
lean_dec(v_toApplicative_140_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_171_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___f_151_; lean_object* v___f_152_; lean_object* v___f_153_; lean_object* v___f_154_; lean_object* v___x_155_; lean_object* v___f_156_; lean_object* v___f_157_; lean_object* v___f_158_; lean_object* v___x_160_; 
v___f_151_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__1));
v___f_152_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___closed__2));
lean_inc_ref(v_toFunctor_144_);
v___f_153_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_153_, 0, v_toFunctor_144_);
v___f_154_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_154_, 0, v_toFunctor_144_);
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v___f_153_);
lean_ctor_set(v___x_155_, 1, v___f_154_);
v___f_156_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_156_, 0, v_toSeqRight_147_);
v___f_157_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_157_, 0, v_toSeqLeft_146_);
v___f_158_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_158_, 0, v_toSeq_145_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 4, v___f_156_);
lean_ctor_set(v___x_149_, 3, v___f_157_);
lean_ctor_set(v___x_149_, 2, v___f_158_);
lean_ctor_set(v___x_149_, 1, v___f_151_);
lean_ctor_set(v___x_149_, 0, v___x_155_);
v___x_160_ = v___x_149_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_155_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v___f_151_);
lean_ctor_set(v_reuseFailAlloc_170_, 2, v___f_158_);
lean_ctor_set(v_reuseFailAlloc_170_, 3, v___f_157_);
lean_ctor_set(v_reuseFailAlloc_170_, 4, v___f_156_);
v___x_160_ = v_reuseFailAlloc_170_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_object* v___x_162_; 
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 1, v___f_152_);
lean_ctor_set(v___x_142_, 0, v___x_160_);
v___x_162_ = v___x_142_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_160_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v___f_152_);
v___x_162_ = v_reuseFailAlloc_169_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___f_166_; lean_object* v___x_2330__overap_167_; lean_object* v___x_168_; 
v___x_163_ = l_StateRefT_x27_instMonad___redArg(v___x_162_);
v___x_164_ = lean_box(0);
v___x_165_ = l_instInhabitedOfMonad___redArg(v___x_163_, v___x_164_);
v___f_166_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_166_, 0, v___x_165_);
v___x_2330__overap_167_ = lean_panic_fn_borrowed(v___f_166_, v_msg_132_);
lean_dec_ref(v___f_166_);
lean_inc(v___y_136_);
lean_inc_ref(v___y_135_);
lean_inc(v___y_134_);
lean_inc_ref(v___y_133_);
v___x_168_ = lean_apply_5(v___x_2330__overap_167_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, lean_box(0));
return v___x_168_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0___boxed(lean_object* v_msg_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0(v_msg_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
return v_res_181_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_185_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__2));
v___x_186_ = lean_unsigned_to_nat(36u);
v___x_187_ = lean_unsigned_to_nat(77u);
v___x_188_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__1));
v___x_189_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__0));
v___x_190_ = l_mkPanicMessageWithDecl(v___x_189_, v___x_188_, v___x_187_, v___x_186_, v___x_185_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1(lean_object* v_snd_191_, lean_object* v_fst_192_, lean_object* v_as_193_, size_t v_sz_194_, size_t v_i_195_, lean_object* v_b_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_a_203_; uint8_t v___x_207_; 
v___x_207_ = lean_usize_dec_lt(v_i_195_, v_sz_194_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; 
lean_dec_ref(v_fst_192_);
v___x_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_208_, 0, v_b_196_);
return v___x_208_;
}
else
{
lean_object* v_fst_209_; lean_object* v_snd_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_259_; 
v_fst_209_ = lean_ctor_get(v_b_196_, 0);
v_snd_210_ = lean_ctor_get(v_b_196_, 1);
v_isSharedCheck_259_ = !lean_is_exclusive(v_b_196_);
if (v_isSharedCheck_259_ == 0)
{
v___x_212_ = v_b_196_;
v_isShared_213_ = v_isSharedCheck_259_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_snd_210_);
lean_inc(v_fst_209_);
lean_dec(v_b_196_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_259_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; uint8_t v___x_215_; lean_object* v_a_221_; uint8_t v___x_222_; lean_object* v___y_224_; lean_object* v___y_225_; lean_object* v___y_252_; 
v___x_214_ = lean_unsigned_to_nat(1u);
v___x_215_ = lean_nat_dec_eq(v_snd_191_, v___x_214_);
v_a_221_ = lean_array_uget_borrowed(v_as_193_, v_i_195_);
v___x_222_ = 1;
switch(lean_obj_tag(v_a_221_))
{
case 0:
{
lean_object* v_code_256_; 
v_code_256_ = lean_ctor_get(v_a_221_, 2);
lean_inc_ref(v_code_256_);
v___y_252_ = v_code_256_;
goto v___jp_251_;
}
case 1:
{
lean_object* v_code_257_; 
v_code_257_ = lean_ctor_get(v_a_221_, 1);
lean_inc_ref(v_code_257_);
v___y_252_ = v_code_257_;
goto v___jp_251_;
}
default: 
{
lean_object* v_code_258_; 
v_code_258_ = lean_ctor_get(v_a_221_, 0);
lean_inc_ref(v_code_258_);
v___y_252_ = v_code_258_;
goto v___jp_251_;
}
}
v___jp_216_:
{
lean_object* v___x_217_; lean_object* v___x_219_; 
v___x_217_ = lean_box(v___x_215_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 1, v___x_217_);
v___x_219_ = v___x_212_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_fst_209_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v___x_217_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
v_a_203_ = v___x_219_;
goto v___jp_202_;
}
}
v___jp_223_:
{
uint8_t v___x_226_; 
v___x_226_ = l_Lean_Compiler_LCNF_Code_alphaEqv(v___x_222_, v___y_224_, v___y_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; 
lean_del_object(v___x_212_);
lean_inc(v_a_221_);
v___x_227_ = lean_array_push(v_fst_209_, v_a_221_);
v___x_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v_snd_210_);
v_a_203_ = v___x_228_;
goto v___jp_202_;
}
else
{
if (lean_obj_tag(v_a_221_) == 1)
{
uint8_t v___x_229_; 
v___x_229_ = lean_unbox(v_snd_210_);
lean_dec(v_snd_210_);
if (v___x_229_ == 0)
{
lean_object* v_code_230_; lean_object* v___x_231_; 
v_code_230_ = lean_ctor_get(v_a_221_, 1);
v___x_231_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_222_, v_code_230_, v___y_198_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_dec_ref_known(v___x_231_, 1);
goto v___jp_216_;
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
lean_del_object(v___x_212_);
lean_dec(v_fst_209_);
lean_dec_ref(v_fst_192_);
v_a_232_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_231_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_231_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
else
{
goto v___jp_216_;
}
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_del_object(v___x_212_);
v___x_240_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___closed__3);
v___x_241_ = l_panic___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__0(v___x_240_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v___x_242_; 
lean_dec_ref_known(v___x_241_, 1);
v___x_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_242_, 0, v_fst_209_);
lean_ctor_set(v___x_242_, 1, v_snd_210_);
v_a_203_ = v___x_242_;
goto v___jp_202_;
}
else
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
lean_dec(v_snd_210_);
lean_dec(v_fst_209_);
lean_dec_ref(v_fst_192_);
v_a_243_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_241_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_241_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_243_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
}
}
v___jp_251_:
{
switch(lean_obj_tag(v_fst_192_))
{
case 0:
{
lean_object* v_code_253_; 
v_code_253_ = lean_ctor_get(v_fst_192_, 2);
lean_inc_ref(v_code_253_);
v___y_224_ = v___y_252_;
v___y_225_ = v_code_253_;
goto v___jp_223_;
}
case 1:
{
lean_object* v_code_254_; 
v_code_254_ = lean_ctor_get(v_fst_192_, 1);
lean_inc_ref(v_code_254_);
v___y_224_ = v___y_252_;
v___y_225_ = v_code_254_;
goto v___jp_223_;
}
default: 
{
lean_object* v_code_255_; 
v_code_255_ = lean_ctor_get(v_fst_192_, 0);
lean_inc_ref(v_code_255_);
v___y_224_ = v___y_252_;
v___y_225_ = v_code_255_;
goto v___jp_223_;
}
}
}
}
}
v___jp_202_:
{
size_t v___x_204_; size_t v___x_205_; 
v___x_204_ = ((size_t)1ULL);
v___x_205_ = lean_usize_add(v_i_195_, v___x_204_);
v_i_195_ = v___x_205_;
v_b_196_ = v_a_203_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1___boxed(lean_object* v_snd_260_, lean_object* v_fst_261_, lean_object* v_as_262_, lean_object* v_sz_263_, lean_object* v_i_264_, lean_object* v_b_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
size_t v_sz_boxed_271_; size_t v_i_boxed_272_; lean_object* v_res_273_; 
v_sz_boxed_271_ = lean_unbox_usize(v_sz_263_);
lean_dec(v_sz_263_);
v_i_boxed_272_ = lean_unbox_usize(v_i_264_);
lean_dec(v_i_264_);
v_res_273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1(v_snd_260_, v_fst_261_, v_as_262_, v_sz_boxed_271_, v_i_boxed_272_, v_b_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec_ref(v_as_262_);
lean_dec(v_snd_260_);
return v_res_273_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__2(lean_object* v___x_274_, lean_object* v_as_275_, size_t v_i_276_, size_t v_stop_277_){
_start:
{
uint8_t v___x_278_; 
v___x_278_ = lean_usize_dec_eq(v_i_276_, v_stop_277_);
if (v___x_278_ == 0)
{
uint8_t v___x_279_; lean_object* v___x_280_; 
v___x_279_ = 1;
v___x_280_ = lean_array_uget_borrowed(v_as_275_, v_i_276_);
if (lean_obj_tag(v___x_280_) == 2)
{
return v___x_279_;
}
else
{
lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_281_ = lean_unsigned_to_nat(1u);
v___x_282_ = lean_nat_dec_le(v___x_274_, v___x_281_);
if (v___x_282_ == 0)
{
size_t v___x_283_; size_t v___x_284_; 
v___x_283_ = ((size_t)1ULL);
v___x_284_ = lean_usize_add(v_i_276_, v___x_283_);
v_i_276_ = v___x_284_;
goto _start;
}
else
{
return v___x_279_;
}
}
}
else
{
uint8_t v___x_286_; 
v___x_286_ = 0;
return v___x_286_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__2___boxed(lean_object* v___x_287_, lean_object* v_as_288_, lean_object* v_i_289_, lean_object* v_stop_290_){
_start:
{
size_t v_i_boxed_291_; size_t v_stop_boxed_292_; uint8_t v_res_293_; lean_object* v_r_294_; 
v_i_boxed_291_ = lean_unbox_usize(v_i_289_);
lean_dec(v_i_289_);
v_stop_boxed_292_ = lean_unbox_usize(v_stop_290_);
lean_dec(v_stop_290_);
v_res_293_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__2(v___x_287_, v_as_288_, v_i_boxed_291_, v_stop_boxed_292_);
lean_dec_ref(v_as_288_);
lean_dec(v___x_287_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt(lean_object* v_alts_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___y_316_; uint8_t v___x_342_; 
v___x_313_ = lean_array_get_size(v_alts_301_);
v___x_314_ = lean_unsigned_to_nat(1u);
v___x_342_ = lean_nat_dec_le(v___x_313_, v___x_314_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_nat_dec_lt(v___x_343_, v___x_313_);
if (v___x_344_ == 0)
{
v___y_316_ = v___x_342_;
goto v___jp_315_;
}
else
{
if (v___x_344_ == 0)
{
v___y_316_ = v___x_342_;
goto v___jp_315_;
}
else
{
size_t v___x_345_; size_t v___x_346_; uint8_t v___x_347_; 
v___x_345_ = ((size_t)0ULL);
v___x_346_ = lean_usize_of_nat(v___x_313_);
v___x_347_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__2(v___x_313_, v_alts_301_, v___x_345_, v___x_346_);
v___y_316_ = v___x_347_;
goto v___jp_315_;
}
}
}
else
{
v___y_316_ = v___x_342_;
goto v___jp_315_;
}
v___jp_307_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_310_, 0, v___y_309_);
v___x_311_ = lean_array_push(v___y_308_, v___x_310_);
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
return v___x_312_;
}
v___jp_315_:
{
if (v___y_316_ == 0)
{
lean_object* v___x_317_; lean_object* v_fst_318_; lean_object* v_snd_319_; uint8_t v___x_320_; 
v___x_317_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs(v_alts_301_);
v_fst_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_fst_318_);
v_snd_319_ = lean_ctor_get(v___x_317_, 1);
lean_inc(v_snd_319_);
lean_dec_ref(v___x_317_);
v___x_320_ = lean_nat_dec_eq(v_snd_319_, v___x_314_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; size_t v_sz_322_; size_t v___x_323_; lean_object* v___x_324_; 
v___x_321_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__1));
v_sz_322_ = lean_array_size(v_alts_301_);
v___x_323_ = ((size_t)0ULL);
lean_inc(v_fst_318_);
v___x_324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt_spec__1(v_snd_319_, v_fst_318_, v_alts_301_, v_sz_322_, v___x_323_, v___x_321_, v_a_302_, v_a_303_, v_a_304_, v_a_305_);
lean_dec_ref(v_alts_301_);
lean_dec(v_snd_319_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v___x_324_, 1);
switch(lean_obj_tag(v_fst_318_))
{
case 0:
{
lean_object* v_fst_326_; lean_object* v_code_327_; 
v_fst_326_ = lean_ctor_get(v_a_325_, 0);
lean_inc(v_fst_326_);
lean_dec(v_a_325_);
v_code_327_ = lean_ctor_get(v_fst_318_, 2);
lean_inc_ref(v_code_327_);
lean_dec_ref_known(v_fst_318_, 3);
v___y_308_ = v_fst_326_;
v___y_309_ = v_code_327_;
goto v___jp_307_;
}
case 1:
{
lean_object* v_fst_328_; lean_object* v_code_329_; 
v_fst_328_ = lean_ctor_get(v_a_325_, 0);
lean_inc(v_fst_328_);
lean_dec(v_a_325_);
v_code_329_ = lean_ctor_get(v_fst_318_, 1);
lean_inc_ref(v_code_329_);
lean_dec_ref_known(v_fst_318_, 2);
v___y_308_ = v_fst_328_;
v___y_309_ = v_code_329_;
goto v___jp_307_;
}
default: 
{
lean_object* v_fst_330_; lean_object* v_code_331_; 
v_fst_330_ = lean_ctor_get(v_a_325_, 0);
lean_inc(v_fst_330_);
lean_dec(v_a_325_);
v_code_331_ = lean_ctor_get(v_fst_318_, 0);
lean_inc_ref(v_code_331_);
lean_dec_ref_known(v_fst_318_, 1);
v___y_308_ = v_fst_330_;
v___y_309_ = v_code_331_;
goto v___jp_307_;
}
}
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
lean_dec(v_fst_318_);
v_a_332_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_324_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_324_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
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
lean_object* v___x_340_; 
lean_dec(v_snd_319_);
lean_dec(v_fst_318_);
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v_alts_301_);
return v___x_340_;
}
}
else
{
lean_object* v___x_341_; 
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v_alts_301_);
return v___x_341_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___boxed(lean_object* v_alts_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt(v_alts_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
return v_res_354_;
}
}
static uint8_t _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0___closed__0(void){
_start:
{
uint8_t v___x_355_; uint8_t v___x_356_; 
v___x_355_ = 1;
v___x_356_ = lean_bool_not(v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0(lean_object* v_as_357_, size_t v_i_358_, size_t v_stop_359_, lean_object* v_b_360_){
_start:
{
lean_object* v___y_362_; uint8_t v___x_366_; 
v___x_366_ = lean_usize_dec_eq(v_i_358_, v_stop_359_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; uint8_t v___y_369_; lean_object* v___y_372_; 
v___x_367_ = lean_array_uget_borrowed(v_as_357_, v_i_358_);
switch(lean_obj_tag(v___x_367_))
{
case 0:
{
lean_object* v_code_375_; 
v_code_375_ = lean_ctor_get(v___x_367_, 2);
lean_inc_ref(v_code_375_);
v___y_372_ = v_code_375_;
goto v___jp_371_;
}
case 1:
{
lean_object* v_code_376_; 
v_code_376_ = lean_ctor_get(v___x_367_, 1);
lean_inc_ref(v_code_376_);
v___y_372_ = v_code_376_;
goto v___jp_371_;
}
default: 
{
lean_object* v_code_377_; 
v_code_377_ = lean_ctor_get(v___x_367_, 0);
lean_inc_ref(v_code_377_);
v___y_372_ = v_code_377_;
goto v___jp_371_;
}
}
v___jp_368_:
{
if (v___y_369_ == 0)
{
v___y_362_ = v_b_360_;
goto v___jp_361_;
}
else
{
lean_object* v___x_370_; 
lean_inc(v___x_367_);
v___x_370_ = lean_array_push(v_b_360_, v___x_367_);
v___y_362_ = v___x_370_;
goto v___jp_361_;
}
}
v___jp_371_:
{
if (lean_obj_tag(v___y_372_) == 6)
{
uint8_t v___x_373_; 
lean_dec_ref_known(v___y_372_, 1);
v___x_373_ = lean_uint8_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0___closed__0);
v___y_369_ = v___x_373_;
goto v___jp_368_;
}
else
{
uint8_t v___x_374_; 
lean_dec_ref(v___y_372_);
v___x_374_ = lean_bool_not(v___x_366_);
v___y_369_ = v___x_374_;
goto v___jp_368_;
}
}
}
else
{
return v_b_360_;
}
v___jp_361_:
{
size_t v___x_363_; size_t v___x_364_; 
v___x_363_ = ((size_t)1ULL);
v___x_364_ = lean_usize_add(v_i_358_, v___x_363_);
v_i_358_ = v___x_364_;
v_b_360_ = v___y_362_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0___boxed(lean_object* v_as_378_, lean_object* v_i_379_, lean_object* v_stop_380_, lean_object* v_b_381_){
_start:
{
size_t v_i_boxed_382_; size_t v_stop_boxed_383_; lean_object* v_res_384_; 
v_i_boxed_382_ = lean_unbox_usize(v_i_379_);
lean_dec(v_i_379_);
v_stop_boxed_383_ = lean_unbox_usize(v_stop_380_);
lean_dec(v_stop_380_);
v_res_384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0(v_as_378_, v_i_boxed_382_, v_stop_boxed_383_, v_b_381_);
lean_dec_ref(v_as_378_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable(lean_object* v_alts_385_){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_386_ = lean_unsigned_to_nat(0u);
v___x_387_ = lean_array_get_size(v_alts_385_);
v___x_388_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt___closed__0));
v___x_389_ = lean_nat_dec_lt(v___x_386_, v___x_387_);
if (v___x_389_ == 0)
{
return v___x_388_;
}
else
{
uint8_t v___x_390_; 
v___x_390_ = lean_nat_dec_le(v___x_387_, v___x_387_);
if (v___x_390_ == 0)
{
if (v___x_389_ == 0)
{
return v___x_388_;
}
else
{
size_t v___x_391_; size_t v___x_392_; lean_object* v___x_393_; 
v___x_391_ = ((size_t)0ULL);
v___x_392_ = lean_usize_of_nat(v___x_387_);
v___x_393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0(v_alts_385_, v___x_391_, v___x_392_, v___x_388_);
return v___x_393_;
}
}
else
{
size_t v___x_394_; size_t v___x_395_; lean_object* v___x_396_; 
v___x_394_ = ((size_t)0ULL);
v___x_395_ = lean_usize_of_nat(v___x_387_);
v___x_396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable_spec__0(v_alts_385_, v___x_394_, v___x_395_, v___x_388_);
return v___x_396_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable___boxed(lean_object* v_alts_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable(v_alts_397_);
lean_dec_ref(v_alts_397_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases(lean_object* v_c_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v_typeName_405_; lean_object* v_resultType_406_; lean_object* v_discr_407_; lean_object* v_alts_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_456_; 
v_typeName_405_ = lean_ctor_get(v_c_399_, 0);
v_resultType_406_ = lean_ctor_get(v_c_399_, 1);
v_discr_407_ = lean_ctor_get(v_c_399_, 2);
v_alts_408_ = lean_ctor_get(v_c_399_, 3);
v_isSharedCheck_456_ = !lean_is_exclusive(v_c_399_);
if (v_isSharedCheck_456_ == 0)
{
v___x_410_ = v_c_399_;
v_isShared_411_ = v_isSharedCheck_456_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_alts_408_);
lean_inc(v_discr_407_);
lean_inc(v_resultType_406_);
lean_inc(v_typeName_405_);
lean_dec(v_c_399_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_456_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v_alts_412_; lean_object* v___x_413_; 
v_alts_412_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_filterUnreachable(v_alts_408_);
lean_dec_ref(v_alts_408_);
v___x_413_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_addDefaultAlt(v_alts_412_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_447_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_447_ == 0)
{
v___x_416_ = v___x_413_;
v_isShared_417_ = v_isSharedCheck_447_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_413_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_447_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_418_ = lean_array_get_size(v_a_414_);
v___x_419_ = lean_unsigned_to_nat(0u);
v___x_420_ = lean_nat_dec_eq(v___x_418_, v___x_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_421_ = lean_unsigned_to_nat(1u);
v___x_422_ = lean_nat_dec_eq(v___x_418_, v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_424_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 3, v_a_414_);
v___x_424_ = v___x_410_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_typeName_405_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_resultType_406_);
lean_ctor_set(v_reuseFailAlloc_429_, 2, v_discr_407_);
lean_ctor_set(v_reuseFailAlloc_429_, 3, v_a_414_);
v___x_424_ = v_reuseFailAlloc_429_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_425_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_425_);
v___x_427_ = v___x_416_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
else
{
lean_object* v___x_430_; 
lean_del_object(v___x_410_);
lean_dec(v_discr_407_);
lean_dec_ref(v_resultType_406_);
lean_dec(v_typeName_405_);
v___x_430_ = lean_array_fget(v_a_414_, v___x_419_);
lean_dec(v_a_414_);
switch(lean_obj_tag(v___x_430_))
{
case 0:
{
lean_object* v_code_431_; lean_object* v___x_433_; 
v_code_431_ = lean_ctor_get(v___x_430_, 2);
lean_inc_ref(v_code_431_);
lean_dec_ref_known(v___x_430_, 3);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v_code_431_);
v___x_433_ = v___x_416_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_code_431_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
case 1:
{
lean_object* v_code_435_; lean_object* v___x_437_; 
v_code_435_ = lean_ctor_get(v___x_430_, 1);
lean_inc_ref(v_code_435_);
lean_dec_ref_known(v___x_430_, 2);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v_code_435_);
v___x_437_ = v___x_416_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_code_435_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
default: 
{
lean_object* v_code_439_; lean_object* v___x_441_; 
v_code_439_ = lean_ctor_get(v___x_430_, 0);
lean_inc_ref(v_code_439_);
lean_dec_ref_known(v___x_430_, 1);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v_code_439_);
v___x_441_ = v___x_416_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_code_439_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
}
else
{
lean_object* v___x_443_; lean_object* v___x_445_; 
lean_dec(v_a_414_);
lean_del_object(v___x_410_);
lean_dec(v_discr_407_);
lean_dec(v_typeName_405_);
v___x_443_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_443_, 0, v_resultType_406_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_443_);
v___x_445_ = v___x_416_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
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
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_del_object(v___x_410_);
lean_dec(v_discr_407_);
lean_dec_ref(v_resultType_406_);
lean_dec(v_typeName_405_);
v_a_448_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_413_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_413_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases___boxed(lean_object* v_c_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases(v_c_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_);
lean_dec(v_a_461_);
lean_dec_ref(v_a_460_);
lean_dec(v_a_459_);
lean_dec_ref(v_a_458_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(lean_object* v_alt_464_, lean_object* v_f_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v___y_472_; 
switch(lean_obj_tag(v_alt_464_))
{
case 0:
{
lean_object* v_code_491_; 
v_code_491_ = lean_ctor_get(v_alt_464_, 2);
lean_inc_ref(v_code_491_);
v___y_472_ = v_code_491_;
goto v___jp_471_;
}
case 1:
{
lean_object* v_code_492_; 
v_code_492_ = lean_ctor_get(v_alt_464_, 1);
lean_inc_ref(v_code_492_);
v___y_472_ = v_code_492_;
goto v___jp_471_;
}
default: 
{
lean_object* v_code_493_; 
v_code_493_ = lean_ctor_get(v_alt_464_, 0);
lean_inc_ref(v_code_493_);
v___y_472_ = v_code_493_;
goto v___jp_471_;
}
}
v___jp_471_:
{
lean_object* v___x_473_; 
lean_inc(v___y_469_);
lean_inc_ref(v___y_468_);
lean_inc(v___y_467_);
lean_inc_ref(v___y_466_);
v___x_473_ = lean_apply_6(v_f_465_, v___y_472_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, lean_box(0));
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_482_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_482_ == 0)
{
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_482_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_482_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_478_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_464_, v_a_474_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_478_);
v___x_480_ = v___x_476_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
lean_dec_ref(v_alt_464_);
v_a_483_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_473_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_473_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg___boxed(lean_object* v_alt_494_, lean_object* v_f_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(v_alt_494_, v_f_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0(uint8_t v_pu_502_, lean_object* v_alt_503_, lean_object* v_f_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(v_alt_503_, v_f_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___boxed(lean_object* v_pu_511_, lean_object* v_alt_512_, lean_object* v_f_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
uint8_t v_pu_boxed_519_; lean_object* v_res_520_; 
v_pu_boxed_519_ = lean_unbox(v_pu_511_);
v_res_520_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0(v_pu_boxed_519_, v_alt_512_, v_f_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(lean_object* v_code_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
switch(lean_obj_tag(v_code_521_))
{
case 0:
{
lean_object* v_decl_527_; lean_object* v_k_528_; lean_object* v___x_529_; 
v_decl_527_ = lean_ctor_get(v_code_521_, 0);
v_k_528_ = lean_ctor_get(v_code_521_, 1);
lean_inc_ref(v_k_528_);
v___x_529_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_528_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_552_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_552_ == 0)
{
v___x_532_ = v___x_529_;
v_isShared_533_ = v_isSharedCheck_552_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_552_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
size_t v___x_534_; size_t v___x_535_; uint8_t v___x_536_; 
v___x_534_ = lean_ptr_addr(v_k_528_);
v___x_535_ = lean_ptr_addr(v_a_530_);
v___x_536_ = lean_usize_dec_eq(v___x_534_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_546_; 
lean_inc_ref(v_decl_527_);
v_isSharedCheck_546_ = !lean_is_exclusive(v_code_521_);
if (v_isSharedCheck_546_ == 0)
{
lean_object* v_unused_547_; lean_object* v_unused_548_; 
v_unused_547_ = lean_ctor_get(v_code_521_, 1);
lean_dec(v_unused_547_);
v_unused_548_ = lean_ctor_get(v_code_521_, 0);
lean_dec(v_unused_548_);
v___x_538_ = v_code_521_;
v_isShared_539_ = v_isSharedCheck_546_;
goto v_resetjp_537_;
}
else
{
lean_dec(v_code_521_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_546_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 1, v_a_530_);
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_decl_527_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_a_530_);
v___x_541_ = v_reuseFailAlloc_545_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_543_; 
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_541_);
v___x_543_ = v___x_532_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
else
{
lean_object* v___x_550_; 
lean_dec(v_a_530_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v_code_521_);
v___x_550_ = v___x_532_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_code_521_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_521_, 2);
return v___x_529_;
}
}
case 2:
{
lean_object* v_decl_553_; lean_object* v_k_554_; lean_object* v_params_555_; lean_object* v_type_556_; lean_object* v_value_557_; lean_object* v___x_558_; 
v_decl_553_ = lean_ctor_get(v_code_521_, 0);
v_k_554_ = lean_ctor_get(v_code_521_, 1);
v_params_555_ = lean_ctor_get(v_decl_553_, 2);
v_type_556_ = lean_ctor_get(v_decl_553_, 3);
v_value_557_ = lean_ctor_get(v_decl_553_, 4);
lean_inc_ref(v_value_557_);
v___x_558_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_value_557_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; uint8_t v___x_560_; lean_object* v___x_561_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_558_, 1);
v___x_560_ = 1;
lean_inc_ref(v_params_555_);
lean_inc_ref(v_type_556_);
lean_inc_ref(v_decl_553_);
v___x_561_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_560_, v_decl_553_, v_type_556_, v_params_555_, v_a_559_, v_a_523_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_563_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_a_562_);
lean_dec_ref_known(v___x_561_, 1);
lean_inc_ref(v_k_554_);
v___x_563_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_554_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_591_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_591_ == 0)
{
v___x_566_ = v___x_563_;
v_isShared_567_ = v_isSharedCheck_591_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_563_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_591_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
uint8_t v___y_569_; size_t v___x_585_; size_t v___x_586_; uint8_t v___x_587_; 
v___x_585_ = lean_ptr_addr(v_k_554_);
v___x_586_ = lean_ptr_addr(v_a_564_);
v___x_587_ = lean_usize_dec_eq(v___x_585_, v___x_586_);
if (v___x_587_ == 0)
{
v___y_569_ = v___x_587_;
goto v___jp_568_;
}
else
{
size_t v___x_588_; size_t v___x_589_; uint8_t v___x_590_; 
v___x_588_ = lean_ptr_addr(v_decl_553_);
v___x_589_ = lean_ptr_addr(v_a_562_);
v___x_590_ = lean_usize_dec_eq(v___x_588_, v___x_589_);
v___y_569_ = v___x_590_;
goto v___jp_568_;
}
v___jp_568_:
{
if (v___y_569_ == 0)
{
lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_579_; 
v_isSharedCheck_579_ = !lean_is_exclusive(v_code_521_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; lean_object* v_unused_581_; 
v_unused_580_ = lean_ctor_get(v_code_521_, 1);
lean_dec(v_unused_580_);
v_unused_581_ = lean_ctor_get(v_code_521_, 0);
lean_dec(v_unused_581_);
v___x_571_ = v_code_521_;
v_isShared_572_ = v_isSharedCheck_579_;
goto v_resetjp_570_;
}
else
{
lean_dec(v_code_521_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_579_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 1, v_a_564_);
lean_ctor_set(v___x_571_, 0, v_a_562_);
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_562_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_a_564_);
v___x_574_ = v_reuseFailAlloc_578_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_576_; 
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_574_);
v___x_576_ = v___x_566_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
else
{
lean_object* v___x_583_; 
lean_dec(v_a_564_);
lean_dec(v_a_562_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v_code_521_);
v___x_583_ = v___x_566_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_code_521_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
}
else
{
lean_dec(v_a_562_);
lean_dec_ref_known(v_code_521_, 2);
return v___x_563_;
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec_ref_known(v_code_521_, 2);
v_a_592_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_561_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_561_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_521_, 2);
return v___x_558_;
}
}
case 4:
{
lean_object* v_cases_600_; lean_object* v_typeName_601_; lean_object* v_resultType_602_; lean_object* v_discr_603_; lean_object* v_alts_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_623_; 
v_cases_600_ = lean_ctor_get(v_code_521_, 0);
lean_inc_ref(v_cases_600_);
lean_dec_ref_known(v_code_521_, 1);
v_typeName_601_ = lean_ctor_get(v_cases_600_, 0);
v_resultType_602_ = lean_ctor_get(v_cases_600_, 1);
v_discr_603_ = lean_ctor_get(v_cases_600_, 2);
v_alts_604_ = lean_ctor_get(v_cases_600_, 3);
v_isSharedCheck_623_ = !lean_is_exclusive(v_cases_600_);
if (v_isSharedCheck_623_ == 0)
{
v___x_606_ = v_cases_600_;
v_isShared_607_ = v_isSharedCheck_623_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_alts_604_);
lean_inc(v_discr_603_);
lean_inc(v_resultType_602_);
lean_inc(v_typeName_601_);
lean_dec(v_cases_600_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_623_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_unsigned_to_nat(0u);
v___x_609_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1(v___x_608_, v_alts_604_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v___x_612_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_a_610_);
lean_dec_ref_known(v___x_609_, 1);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 3, v_a_610_);
v___x_612_ = v___x_606_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_typeName_601_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_resultType_602_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v_discr_603_);
lean_ctor_set(v_reuseFailAlloc_614_, 3, v_a_610_);
v___x_612_ = v_reuseFailAlloc_614_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_613_; 
v___x_613_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_simplifyCases(v___x_612_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
return v___x_613_;
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
lean_del_object(v___x_606_);
lean_dec(v_discr_603_);
lean_dec_ref(v_resultType_602_);
lean_dec(v_typeName_601_);
v_a_615_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_609_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_609_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_624_; lean_object* v_i_625_; lean_object* v_y_626_; lean_object* v_k_627_; lean_object* v___x_628_; 
v_fvarId_624_ = lean_ctor_get(v_code_521_, 0);
v_i_625_ = lean_ctor_get(v_code_521_, 1);
v_y_626_ = lean_ctor_get(v_code_521_, 2);
v_k_627_ = lean_ctor_get(v_code_521_, 3);
lean_inc_ref(v_k_627_);
v___x_628_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_627_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_653_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_653_ == 0)
{
v___x_631_ = v___x_628_;
v_isShared_632_ = v_isSharedCheck_653_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_628_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_653_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
size_t v___x_633_; size_t v___x_634_; uint8_t v___x_635_; 
v___x_633_ = lean_ptr_addr(v_k_627_);
v___x_634_ = lean_ptr_addr(v_a_629_);
v___x_635_ = lean_usize_dec_eq(v___x_633_, v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_645_; 
lean_inc(v_y_626_);
lean_inc(v_i_625_);
lean_inc(v_fvarId_624_);
v_isSharedCheck_645_ = !lean_is_exclusive(v_code_521_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; lean_object* v_unused_647_; lean_object* v_unused_648_; lean_object* v_unused_649_; 
v_unused_646_ = lean_ctor_get(v_code_521_, 3);
lean_dec(v_unused_646_);
v_unused_647_ = lean_ctor_get(v_code_521_, 2);
lean_dec(v_unused_647_);
v_unused_648_ = lean_ctor_get(v_code_521_, 1);
lean_dec(v_unused_648_);
v_unused_649_ = lean_ctor_get(v_code_521_, 0);
lean_dec(v_unused_649_);
v___x_637_ = v_code_521_;
v_isShared_638_ = v_isSharedCheck_645_;
goto v_resetjp_636_;
}
else
{
lean_dec(v_code_521_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_645_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 3, v_a_629_);
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_fvarId_624_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_i_625_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v_y_626_);
lean_ctor_set(v_reuseFailAlloc_644_, 3, v_a_629_);
v___x_640_ = v_reuseFailAlloc_644_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_642_; 
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_640_);
v___x_642_ = v___x_631_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
else
{
lean_object* v___x_651_; 
lean_dec(v_a_629_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v_code_521_);
v___x_651_ = v___x_631_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_code_521_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_521_, 4);
return v___x_628_;
}
}
case 8:
{
lean_object* v_fvarId_654_; lean_object* v_i_655_; lean_object* v_y_656_; lean_object* v_k_657_; lean_object* v___x_658_; 
v_fvarId_654_ = lean_ctor_get(v_code_521_, 0);
v_i_655_ = lean_ctor_get(v_code_521_, 1);
v_y_656_ = lean_ctor_get(v_code_521_, 2);
v_k_657_ = lean_ctor_get(v_code_521_, 3);
lean_inc_ref(v_k_657_);
v___x_658_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_657_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_683_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_683_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_683_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_683_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
size_t v___x_663_; size_t v___x_664_; uint8_t v___x_665_; 
v___x_663_ = lean_ptr_addr(v_k_657_);
v___x_664_ = lean_ptr_addr(v_a_659_);
v___x_665_ = lean_usize_dec_eq(v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_675_; 
lean_inc(v_y_656_);
lean_inc(v_i_655_);
lean_inc(v_fvarId_654_);
v_isSharedCheck_675_ = !lean_is_exclusive(v_code_521_);
if (v_isSharedCheck_675_ == 0)
{
lean_object* v_unused_676_; lean_object* v_unused_677_; lean_object* v_unused_678_; lean_object* v_unused_679_; 
v_unused_676_ = lean_ctor_get(v_code_521_, 3);
lean_dec(v_unused_676_);
v_unused_677_ = lean_ctor_get(v_code_521_, 2);
lean_dec(v_unused_677_);
v_unused_678_ = lean_ctor_get(v_code_521_, 1);
lean_dec(v_unused_678_);
v_unused_679_ = lean_ctor_get(v_code_521_, 0);
lean_dec(v_unused_679_);
v___x_667_ = v_code_521_;
v_isShared_668_ = v_isSharedCheck_675_;
goto v_resetjp_666_;
}
else
{
lean_dec(v_code_521_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_675_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 3, v_a_659_);
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_fvarId_654_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_i_655_);
lean_ctor_set(v_reuseFailAlloc_674_, 2, v_y_656_);
lean_ctor_set(v_reuseFailAlloc_674_, 3, v_a_659_);
v___x_670_ = v_reuseFailAlloc_674_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_672_; 
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_670_);
v___x_672_ = v___x_661_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
else
{
lean_object* v___x_681_; 
lean_dec(v_a_659_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v_code_521_);
v___x_681_ = v___x_661_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_code_521_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_521_, 4);
return v___x_658_;
}
}
case 9:
{
lean_object* v_fvarId_684_; lean_object* v_i_685_; lean_object* v_offset_686_; lean_object* v_y_687_; lean_object* v_ty_688_; lean_object* v_k_689_; lean_object* v___x_690_; 
v_fvarId_684_ = lean_ctor_get(v_code_521_, 0);
v_i_685_ = lean_ctor_get(v_code_521_, 1);
v_offset_686_ = lean_ctor_get(v_code_521_, 2);
v_y_687_ = lean_ctor_get(v_code_521_, 3);
v_ty_688_ = lean_ctor_get(v_code_521_, 4);
v_k_689_ = lean_ctor_get(v_code_521_, 5);
lean_inc_ref(v_k_689_);
v___x_690_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_689_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_717_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_717_ == 0)
{
v___x_693_ = v___x_690_;
v_isShared_694_ = v_isSharedCheck_717_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_690_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_717_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
size_t v___x_695_; size_t v___x_696_; uint8_t v___x_697_; 
v___x_695_ = lean_ptr_addr(v_k_689_);
v___x_696_ = lean_ptr_addr(v_a_691_);
v___x_697_ = lean_usize_dec_eq(v___x_695_, v___x_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_707_; 
lean_inc_ref(v_ty_688_);
lean_inc(v_y_687_);
lean_inc(v_offset_686_);
lean_inc(v_i_685_);
lean_inc(v_fvarId_684_);
v_isSharedCheck_707_ = !lean_is_exclusive(v_code_521_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; lean_object* v_unused_709_; lean_object* v_unused_710_; lean_object* v_unused_711_; lean_object* v_unused_712_; lean_object* v_unused_713_; 
v_unused_708_ = lean_ctor_get(v_code_521_, 5);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_code_521_, 4);
lean_dec(v_unused_709_);
v_unused_710_ = lean_ctor_get(v_code_521_, 3);
lean_dec(v_unused_710_);
v_unused_711_ = lean_ctor_get(v_code_521_, 2);
lean_dec(v_unused_711_);
v_unused_712_ = lean_ctor_get(v_code_521_, 1);
lean_dec(v_unused_712_);
v_unused_713_ = lean_ctor_get(v_code_521_, 0);
lean_dec(v_unused_713_);
v___x_699_ = v_code_521_;
v_isShared_700_ = v_isSharedCheck_707_;
goto v_resetjp_698_;
}
else
{
lean_dec(v_code_521_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_707_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 5, v_a_691_);
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_fvarId_684_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_i_685_);
lean_ctor_set(v_reuseFailAlloc_706_, 2, v_offset_686_);
lean_ctor_set(v_reuseFailAlloc_706_, 3, v_y_687_);
lean_ctor_set(v_reuseFailAlloc_706_, 4, v_ty_688_);
lean_ctor_set(v_reuseFailAlloc_706_, 5, v_a_691_);
v___x_702_ = v_reuseFailAlloc_706_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_704_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_702_);
v___x_704_ = v___x_693_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
else
{
lean_object* v___x_715_; 
lean_dec(v_a_691_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v_code_521_);
v___x_715_ = v___x_693_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_code_521_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_521_, 6);
return v___x_690_;
}
}
case 10:
{
lean_object* v_fvarId_718_; lean_object* v_cidx_719_; lean_object* v_k_720_; lean_object* v___x_721_; 
v_fvarId_718_ = lean_ctor_get(v_code_521_, 0);
v_cidx_719_ = lean_ctor_get(v_code_521_, 1);
v_k_720_ = lean_ctor_get(v_code_521_, 2);
lean_inc_ref(v_k_720_);
v___x_721_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_720_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_745_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_745_ == 0)
{
v___x_724_ = v___x_721_;
v_isShared_725_ = v_isSharedCheck_745_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_721_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_745_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
size_t v___x_726_; size_t v___x_727_; uint8_t v___x_728_; 
v___x_726_ = lean_ptr_addr(v_k_720_);
v___x_727_ = lean_ptr_addr(v_a_722_);
v___x_728_ = lean_usize_dec_eq(v___x_726_, v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_738_; 
lean_inc(v_cidx_719_);
lean_inc(v_fvarId_718_);
v_isSharedCheck_738_ = !lean_is_exclusive(v_code_521_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; lean_object* v_unused_740_; lean_object* v_unused_741_; 
v_unused_739_ = lean_ctor_get(v_code_521_, 2);
lean_dec(v_unused_739_);
v_unused_740_ = lean_ctor_get(v_code_521_, 1);
lean_dec(v_unused_740_);
v_unused_741_ = lean_ctor_get(v_code_521_, 0);
lean_dec(v_unused_741_);
v___x_730_ = v_code_521_;
v_isShared_731_ = v_isSharedCheck_738_;
goto v_resetjp_729_;
}
else
{
lean_dec(v_code_521_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_738_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 2, v_a_722_);
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_fvarId_718_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_cidx_719_);
lean_ctor_set(v_reuseFailAlloc_737_, 2, v_a_722_);
v___x_733_ = v_reuseFailAlloc_737_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_735_; 
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v___x_733_);
v___x_735_ = v___x_724_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
else
{
lean_object* v___x_743_; 
lean_dec(v_a_722_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v_code_521_);
v___x_743_ = v___x_724_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_code_521_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_521_, 3);
return v___x_721_;
}
}
case 11:
{
lean_object* v_fvarId_746_; lean_object* v_n_747_; uint8_t v_check_748_; uint8_t v_persistent_749_; lean_object* v_k_750_; lean_object* v___x_751_; 
v_fvarId_746_ = lean_ctor_get(v_code_521_, 0);
v_n_747_ = lean_ctor_get(v_code_521_, 1);
v_check_748_ = lean_ctor_get_uint8(v_code_521_, sizeof(void*)*3);
v_persistent_749_ = lean_ctor_get_uint8(v_code_521_, sizeof(void*)*3 + 1);
v_k_750_ = lean_ctor_get(v_code_521_, 2);
lean_inc_ref(v_k_750_);
v___x_751_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_750_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_775_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_775_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_775_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_775_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
size_t v___x_756_; size_t v___x_757_; uint8_t v___x_758_; 
v___x_756_ = lean_ptr_addr(v_k_750_);
v___x_757_ = lean_ptr_addr(v_a_752_);
v___x_758_ = lean_usize_dec_eq(v___x_756_, v___x_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_768_; 
lean_inc(v_n_747_);
lean_inc(v_fvarId_746_);
v_isSharedCheck_768_ = !lean_is_exclusive(v_code_521_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; lean_object* v_unused_770_; lean_object* v_unused_771_; 
v_unused_769_ = lean_ctor_get(v_code_521_, 2);
lean_dec(v_unused_769_);
v_unused_770_ = lean_ctor_get(v_code_521_, 1);
lean_dec(v_unused_770_);
v_unused_771_ = lean_ctor_get(v_code_521_, 0);
lean_dec(v_unused_771_);
v___x_760_ = v_code_521_;
v_isShared_761_ = v_isSharedCheck_768_;
goto v_resetjp_759_;
}
else
{
lean_dec(v_code_521_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_768_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 2, v_a_752_);
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_fvarId_746_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_n_747_);
lean_ctor_set(v_reuseFailAlloc_767_, 2, v_a_752_);
lean_ctor_set_uint8(v_reuseFailAlloc_767_, sizeof(void*)*3, v_check_748_);
lean_ctor_set_uint8(v_reuseFailAlloc_767_, sizeof(void*)*3 + 1, v_persistent_749_);
v___x_763_ = v_reuseFailAlloc_767_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
lean_object* v___x_765_; 
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_763_);
v___x_765_ = v___x_754_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_763_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
else
{
lean_object* v___x_773_; 
lean_dec(v_a_752_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v_code_521_);
v___x_773_ = v___x_754_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_code_521_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_521_, 3);
return v___x_751_;
}
}
case 12:
{
lean_object* v_fvarId_776_; lean_object* v_n_777_; uint8_t v_check_778_; uint8_t v_persistent_779_; lean_object* v_objs_x3f_780_; lean_object* v_k_781_; lean_object* v___x_782_; 
v_fvarId_776_ = lean_ctor_get(v_code_521_, 0);
v_n_777_ = lean_ctor_get(v_code_521_, 1);
v_check_778_ = lean_ctor_get_uint8(v_code_521_, sizeof(void*)*4);
v_persistent_779_ = lean_ctor_get_uint8(v_code_521_, sizeof(void*)*4 + 1);
v_objs_x3f_780_ = lean_ctor_get(v_code_521_, 2);
v_k_781_ = lean_ctor_get(v_code_521_, 3);
lean_inc_ref(v_k_781_);
v___x_782_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_781_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_807_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_807_ == 0)
{
v___x_785_ = v___x_782_;
v_isShared_786_ = v_isSharedCheck_807_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_782_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_807_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
size_t v___x_787_; size_t v___x_788_; uint8_t v___x_789_; 
v___x_787_ = lean_ptr_addr(v_k_781_);
v___x_788_ = lean_ptr_addr(v_a_783_);
v___x_789_ = lean_usize_dec_eq(v___x_787_, v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_799_; 
lean_inc(v_objs_x3f_780_);
lean_inc(v_n_777_);
lean_inc(v_fvarId_776_);
v_isSharedCheck_799_ = !lean_is_exclusive(v_code_521_);
if (v_isSharedCheck_799_ == 0)
{
lean_object* v_unused_800_; lean_object* v_unused_801_; lean_object* v_unused_802_; lean_object* v_unused_803_; 
v_unused_800_ = lean_ctor_get(v_code_521_, 3);
lean_dec(v_unused_800_);
v_unused_801_ = lean_ctor_get(v_code_521_, 2);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v_code_521_, 1);
lean_dec(v_unused_802_);
v_unused_803_ = lean_ctor_get(v_code_521_, 0);
lean_dec(v_unused_803_);
v___x_791_ = v_code_521_;
v_isShared_792_ = v_isSharedCheck_799_;
goto v_resetjp_790_;
}
else
{
lean_dec(v_code_521_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_799_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 3, v_a_783_);
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_fvarId_776_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_n_777_);
lean_ctor_set(v_reuseFailAlloc_798_, 2, v_objs_x3f_780_);
lean_ctor_set(v_reuseFailAlloc_798_, 3, v_a_783_);
lean_ctor_set_uint8(v_reuseFailAlloc_798_, sizeof(void*)*4, v_check_778_);
lean_ctor_set_uint8(v_reuseFailAlloc_798_, sizeof(void*)*4 + 1, v_persistent_779_);
v___x_794_ = v_reuseFailAlloc_798_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_796_; 
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_794_);
v___x_796_ = v___x_785_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_794_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
else
{
lean_object* v___x_805_; 
lean_dec(v_a_783_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v_code_521_);
v___x_805_ = v___x_785_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_code_521_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_521_, 4);
return v___x_782_;
}
}
case 13:
{
lean_object* v_fvarId_808_; lean_object* v_k_809_; lean_object* v___x_810_; 
v_fvarId_808_ = lean_ctor_get(v_code_521_, 0);
v_k_809_ = lean_ctor_get(v_code_521_, 1);
lean_inc_ref(v_k_809_);
v___x_810_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_k_809_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_833_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_833_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_833_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_833_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
size_t v___x_815_; size_t v___x_816_; uint8_t v___x_817_; 
v___x_815_ = lean_ptr_addr(v_k_809_);
v___x_816_ = lean_ptr_addr(v_a_811_);
v___x_817_ = lean_usize_dec_eq(v___x_815_, v___x_816_);
if (v___x_817_ == 0)
{
lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_827_; 
lean_inc(v_fvarId_808_);
v_isSharedCheck_827_ = !lean_is_exclusive(v_code_521_);
if (v_isSharedCheck_827_ == 0)
{
lean_object* v_unused_828_; lean_object* v_unused_829_; 
v_unused_828_ = lean_ctor_get(v_code_521_, 1);
lean_dec(v_unused_828_);
v_unused_829_ = lean_ctor_get(v_code_521_, 0);
lean_dec(v_unused_829_);
v___x_819_ = v_code_521_;
v_isShared_820_ = v_isSharedCheck_827_;
goto v_resetjp_818_;
}
else
{
lean_dec(v_code_521_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_827_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 1, v_a_811_);
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_fvarId_808_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_a_811_);
v___x_822_ = v_reuseFailAlloc_826_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_824_; 
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_822_);
v___x_824_ = v___x_813_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v___x_831_; 
lean_dec(v_a_811_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v_code_521_);
v___x_831_ = v___x_813_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_code_521_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_521_, 2);
return v___x_810_;
}
}
default: 
{
lean_object* v___x_834_; 
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v_code_521_);
return v___x_834_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase___boxed(lean_object* v_code_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase(v_code_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_);
lean_dec(v_a_839_);
lean_dec_ref(v_a_838_);
lean_dec(v_a_837_);
lean_dec_ref(v_a_836_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1(lean_object* v_i_842_, lean_object* v_as_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_849_ = lean_array_get_size(v_as_843_);
v___x_850_ = lean_nat_dec_lt(v_i_842_, v___x_849_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; 
lean_dec(v_i_842_);
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v_as_843_);
return v___x_851_;
}
else
{
lean_object* v___f_852_; lean_object* v_a_853_; lean_object* v___x_854_; 
v___f_852_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase___boxed), 6, 0);
v_a_853_ = lean_array_fget_borrowed(v_as_843_, v_i_842_);
lean_inc(v_a_853_);
v___x_854_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__0___redArg(v_a_853_, v___f_852_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; size_t v___x_856_; size_t v___x_857_; uint8_t v___x_858_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
v___x_856_ = lean_ptr_addr(v_a_853_);
v___x_857_ = lean_ptr_addr(v_a_855_);
v___x_858_ = lean_usize_dec_eq(v___x_856_, v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_859_ = lean_unsigned_to_nat(1u);
v___x_860_ = lean_nat_add(v_i_842_, v___x_859_);
v___x_861_ = lean_array_fset(v_as_843_, v_i_842_, v_a_855_);
lean_dec(v_i_842_);
v_i_842_ = v___x_860_;
v_as_843_ = v___x_861_;
goto _start;
}
else
{
lean_object* v___x_863_; lean_object* v___x_864_; 
lean_dec(v_a_855_);
v___x_863_ = lean_unsigned_to_nat(1u);
v___x_864_ = lean_nat_add(v_i_842_, v___x_863_);
lean_dec(v_i_842_);
v_i_842_ = v___x_864_;
goto _start;
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec_ref(v_as_843_);
lean_dec(v_i_842_);
v_a_866_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_854_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_854_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1___boxed(lean_object* v_i_874_, lean_object* v_as_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Code_simpCase_spec__1(v_i_874_, v_as_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(lean_object* v_f_882_, lean_object* v_v_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
if (lean_obj_tag(v_v_883_) == 0)
{
lean_object* v_code_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_913_; 
v_code_889_ = lean_ctor_get(v_v_883_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v_v_883_);
if (v_isSharedCheck_913_ == 0)
{
v___x_891_ = v_v_883_;
v_isShared_892_ = v_isSharedCheck_913_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_code_889_);
lean_dec(v_v_883_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_913_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; 
lean_inc(v___y_887_);
lean_inc_ref(v___y_886_);
lean_inc(v___y_885_);
lean_inc_ref(v___y_884_);
v___x_893_ = lean_apply_6(v_f_882_, v_code_889_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, lean_box(0));
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_904_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_904_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_904_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_904_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v_a_894_);
v___x_899_ = v___x_891_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_903_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_901_; 
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_899_);
v___x_901_ = v___x_896_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
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
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_del_object(v___x_891_);
v_a_905_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_893_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_893_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
else
{
lean_object* v___x_914_; 
lean_dec_ref(v_f_882_);
v___x_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_914_, 0, v_v_883_);
return v___x_914_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg___boxed(lean_object* v_f_915_, lean_object* v_v_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(v_f_915_, v_v_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0(uint8_t v_pu_923_, lean_object* v_f_924_, lean_object* v_v_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(v_f_924_, v_v_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___boxed(lean_object* v_pu_932_, lean_object* v_f_933_, lean_object* v_v_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
uint8_t v_pu_boxed_940_; lean_object* v_res_941_; 
v_pu_boxed_940_ = lean_unbox(v_pu_932_);
v_res_941_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0(v_pu_boxed_940_, v_f_933_, v_v_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase(lean_object* v_decl_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v_toSignature_949_; lean_object* v_value_950_; uint8_t v_recursive_951_; lean_object* v_inlineAttr_x3f_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_977_; 
v_toSignature_949_ = lean_ctor_get(v_decl_943_, 0);
v_value_950_ = lean_ctor_get(v_decl_943_, 1);
v_recursive_951_ = lean_ctor_get_uint8(v_decl_943_, sizeof(void*)*3);
v_inlineAttr_x3f_952_ = lean_ctor_get(v_decl_943_, 2);
v_isSharedCheck_977_ = !lean_is_exclusive(v_decl_943_);
if (v_isSharedCheck_977_ == 0)
{
v___x_954_ = v_decl_943_;
v_isShared_955_ = v_isSharedCheck_977_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_inlineAttr_x3f_952_);
lean_inc(v_value_950_);
lean_inc(v_toSignature_949_);
lean_dec(v_decl_943_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_977_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___f_956_; lean_object* v___x_957_; 
v___f_956_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___closed__0));
v___x_957_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase_spec__0___redArg(v___f_956_, v_value_950_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_968_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_968_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_968_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_968_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 1, v_a_958_);
v___x_963_ = v___x_954_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_toSignature_949_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_a_958_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v_inlineAttr_x3f_952_);
lean_ctor_set_uint8(v_reuseFailAlloc_967_, sizeof(void*)*3, v_recursive_951_);
v___x_963_ = v_reuseFailAlloc_967_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_965_; 
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v___x_963_);
v___x_965_ = v___x_960_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
lean_del_object(v___x_954_);
lean_dec(v_inlineAttr_x3f_952_);
lean_dec_ref(v_toSignature_949_);
v_a_969_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_957_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_957_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase___boxed(lean_object* v_decl_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_Decl_simpCase(v_decl_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
return v_res_984_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0(lean_object* v_as_985_, size_t v_i_986_, size_t v_stop_987_){
_start:
{
uint8_t v___x_988_; 
v___x_988_ = lean_usize_dec_eq(v_i_986_, v_stop_987_);
if (v___x_988_ == 0)
{
uint8_t v___x_989_; lean_object* v___x_990_; 
v___x_989_ = 1;
v___x_990_ = lean_array_uget_borrowed(v_as_985_, v_i_986_);
if (lean_obj_tag(v___x_990_) == 2)
{
return v___x_989_;
}
else
{
if (v___x_988_ == 0)
{
size_t v___x_991_; size_t v___x_992_; 
v___x_991_ = ((size_t)1ULL);
v___x_992_ = lean_usize_add(v_i_986_, v___x_991_);
v_i_986_ = v___x_992_;
goto _start;
}
else
{
return v___x_989_;
}
}
}
else
{
uint8_t v___x_994_; 
v___x_994_ = 0;
return v___x_994_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0___boxed(lean_object* v_as_995_, lean_object* v_i_996_, lean_object* v_stop_997_){
_start:
{
size_t v_i_boxed_998_; size_t v_stop_boxed_999_; uint8_t v_res_1000_; lean_object* v_r_1001_; 
v_i_boxed_998_ = lean_unbox_usize(v_i_996_);
lean_dec(v_i_996_);
v_stop_boxed_999_ = lean_unbox_usize(v_stop_997_);
lean_dec(v_stop_997_);
v_res_1000_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0(v_as_995_, v_i_boxed_998_, v_stop_boxed_999_);
lean_dec_ref(v_as_995_);
v_r_1001_ = lean_box(v_res_1000_);
return v_r_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ensureHasDefault(lean_object* v_alts_1002_){
_start:
{
lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1021_; 
v___x_1008_ = lean_unsigned_to_nat(0u);
v___x_1009_ = lean_array_get_size(v_alts_1002_);
v___x_1021_ = lean_nat_dec_lt(v___x_1008_, v___x_1009_);
if (v___x_1021_ == 0)
{
goto v___jp_1010_;
}
else
{
if (v___x_1021_ == 0)
{
goto v___jp_1010_;
}
else
{
size_t v___x_1022_; size_t v___x_1023_; uint8_t v___x_1024_; 
v___x_1022_ = ((size_t)0ULL);
v___x_1023_ = lean_usize_of_nat(v___x_1009_);
v___x_1024_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ensureHasDefault_spec__0(v_alts_1002_, v___x_1022_, v___x_1023_);
if (v___x_1024_ == 0)
{
goto v___jp_1010_;
}
else
{
return v_alts_1002_;
}
}
}
v___jp_1003_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___y_1005_);
v___x_1007_ = lean_array_push(v___y_1004_, v___x_1006_);
return v___x_1007_;
}
v___jp_1010_:
{
lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___x_1011_ = lean_unsigned_to_nat(2u);
v___x_1012_ = lean_nat_dec_lt(v___x_1009_, v___x_1011_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v_last_1016_; lean_object* v_alts_1017_; 
v___x_1013_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0, &l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0_once, _init_l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_getMaxOccs_getNumOccsOf___closed__0);
v___x_1014_ = lean_unsigned_to_nat(1u);
v___x_1015_ = lean_nat_sub(v___x_1009_, v___x_1014_);
v_last_1016_ = lean_array_get(v___x_1013_, v_alts_1002_, v___x_1015_);
lean_dec(v___x_1015_);
v_alts_1017_ = lean_array_pop(v_alts_1002_);
switch(lean_obj_tag(v_last_1016_))
{
case 0:
{
lean_object* v_code_1018_; 
v_code_1018_ = lean_ctor_get(v_last_1016_, 2);
lean_inc_ref(v_code_1018_);
lean_dec_ref_known(v_last_1016_, 3);
v___y_1004_ = v_alts_1017_;
v___y_1005_ = v_code_1018_;
goto v___jp_1003_;
}
case 1:
{
lean_object* v_code_1019_; 
v_code_1019_ = lean_ctor_get(v_last_1016_, 1);
lean_inc_ref(v_code_1019_);
lean_dec_ref_known(v_last_1016_, 2);
v___y_1004_ = v_alts_1017_;
v___y_1005_ = v_code_1019_;
goto v___jp_1003_;
}
default: 
{
lean_object* v_code_1020_; 
v_code_1020_ = lean_ctor_get(v_last_1016_, 0);
lean_inc_ref(v_code_1020_);
lean_dec_ref_known(v_last_1016_, 1);
v___y_1004_ = v_alts_1017_;
v___y_1005_ = v_code_1020_;
goto v___jp_1003_;
}
}
}
else
{
return v_alts_1002_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_simpCase___closed__3(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1029_ = lean_unsigned_to_nat(0u);
v___x_1030_ = ((lean_object*)(l_Lean_Compiler_LCNF_simpCase___closed__2));
v___x_1031_ = 2;
v___x_1032_ = ((lean_object*)(l_Lean_Compiler_LCNF_simpCase___closed__1));
v___x_1033_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_1032_, v___x_1031_, v___x_1030_, v___x_1029_);
return v___x_1033_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_simpCase(void){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_obj_once(&l_Lean_Compiler_LCNF_simpCase___closed__3, &l_Lean_Compiler_LCNF_simpCase___closed__3_once, _init_l_Lean_Compiler_LCNF_simpCase___closed__3);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1105_; uint8_t v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1105_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_));
v___x_1106_ = 1;
v___x_1107_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_));
v___x_1108_ = l_Lean_registerTraceClass(v___x_1105_, v___x_1106_, v___x_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2____boxed(lean_object* v_a_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_();
return v_res_1110_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_AlphaEqv(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_SimpCase(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_AlphaEqv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_simpCase = _init_l_Lean_Compiler_LCNF_simpCase();
lean_mark_persistent(l_Lean_Compiler_LCNF_simpCase);
res = l___private_Lean_Compiler_LCNF_SimpCase_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpCase_1808010913____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_SimpCase(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_AlphaEqv(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_SimpCase(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_AlphaEqv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_SimpCase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_SimpCase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_SimpCase(builtin);
}
#ifdef __cplusplus
}
#endif
