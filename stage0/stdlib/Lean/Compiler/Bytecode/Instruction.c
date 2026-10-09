// Lean compiler output
// Module: Lean.Compiler.Bytecode.Instruction
// Imports: public import Lean.Compiler.Bytecode.Basic import Init.Omega
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
uint32_t lean_uint32_lor(uint32_t, uint32_t);
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
uint32_t lean_int32_of_nat(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint32_t lean_int32_add(uint32_t, uint32_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_uint32_to_uint8(uint32_t);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
uint32_t lean_uint32_shift_right(uint32_t, uint32_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_empty_byte_array(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Nat_toDigits(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_replicateTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_mk(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_uint8_to_uint32(uint8_t);
uint32_t lean_uint32_land(uint32_t, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_BitVec_toHex(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_instInhabitedInstruction_default;
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_instInhabitedInstruction;
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_maxUConst;
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_maxNConst;
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_uconst(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_uconst___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_nconst(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_nconst___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_move(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_move___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_ret(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_ret___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_call(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_call___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_retcall(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_retcall___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_computeScalar(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_computeScalar___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_allocCtor(uint32_t, uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_allocCtor___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_proj(uint32_t, uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_proj___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_uproj(uint32_t, uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_uproj___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_sproj8(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sproj8___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_sproj16(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sproj16___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_sproj32(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sproj32___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_sproj64(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sproj64___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_set(uint32_t, uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_set___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_uset(uint32_t, uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_uset___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_sset8(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sset8___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_sset16(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sset16___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_sset32(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sset32___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_sset64(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sset64___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_boxSmall(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_boxSmall___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_boxUInt32(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_boxUInt32___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_boxUInt64(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_boxUInt64___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_boxUSize(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_boxUSize___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_boxFloat(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_boxFloat___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_boxFloat32(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_boxFloat32___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_unboxSmall(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_unboxSmall___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_unboxUInt32(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_unboxUInt32___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_unboxUInt64(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_unboxUInt64___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_unboxUSize(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_unboxUSize___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_unboxFloat(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_unboxFloat___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_unboxFloat32(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_unboxFloat32___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_inc(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_inc___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_dec(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_dec___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_isShared(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_isShared___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_loadTag(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_loadTag___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_jumpTable(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_jumpTable___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_setTag(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_setTag___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_loadConst(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_loadConst___boxed(lean_object*);
static lean_once_cell_t l_Lean_Compiler_Bytecode_Instruction_ifTag___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Lean_Compiler_Bytecode_Instruction_ifTag___closed__0;
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_ifTag(uint32_t, uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_ifTag___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_Bytecode_Instruction_jump___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Lean_Compiler_Bytecode_Instruction_jump___closed__0;
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_jump(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_jump___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_nojump;
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_app(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_app___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_pap(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_pap___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_del(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_del___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_reset(uint32_t, uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_reset___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_reuse(uint32_t, uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_reuse___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_storeCache(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_storeCache___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_skipIfCached(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_skipIfCached___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_declConst(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_declConst___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_assemblerInternal(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_assemblerInternal___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_pushInstr(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_pushInstr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_assemble_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_assemble_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_assemble(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_assemble___boxed(lean_object*);
static const lean_string_object l_Lean_Compiler_Bytecode_addrToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "0x"};
static const lean_object* l_Lean_Compiler_Bytecode_addrToString___closed__0 = (const lean_object*)&l_Lean_Compiler_Bytecode_addrToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_addrToString___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_addrToString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_addrToString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Compiler_Bytecode_Instruction_toString_spec__0(lean_object*);
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "decl_const R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__0 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__0_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " @"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__1 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__1_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "skip_if_cached "};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__2 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__2_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "store_cache R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__3 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__3_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reuse R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__4 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__4_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__5 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__5_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "reset "};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__6 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__6_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__7 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__7_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "del R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__8 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__8_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pap "};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__9 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__9_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " #"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__10 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__10_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "app "};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__11 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__11_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "jump "};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__12 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__12_value;
static lean_once_cell_t l_Lean_Compiler_Bytecode_Instruction_toString___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__13;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "if_tag R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__14 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__14_value;
static lean_once_cell_t l_Lean_Compiler_Bytecode_Instruction_toString___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__15;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "load_const #"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__16 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__16_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "set_tag R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__17 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__17_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "table R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__18 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__18_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "load_tag R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__19 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__19_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "is_shared R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__20 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__20_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "dec R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__21 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__21_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "inc R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__22 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__22_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unbox_f32 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__23 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__23_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unbox_f64 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__24 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__24_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unbox_usz R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__25 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__25_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "unbox64 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__26 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__26_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "unbox32 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__27 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__27_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "unbox R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__28 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__28_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "box_f32 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__29 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__29_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "box_f64 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__30 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__30_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "box_usz R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__31 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__31_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "box64 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__32 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__32_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "box32 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__33 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__33_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "box R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__34 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__34_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "sset64 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__35 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__35_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "sset32 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__36 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__36_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "sset16 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__37 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__37_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "sset8 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__38 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__38_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "uset R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__39 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__39_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "set R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__40 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__40_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "sproj64 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__41 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__41_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "sproj32 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__42 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__42_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "sproj16 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__43 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__43_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "sproj8 R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__44 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__44_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "uproj R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__45 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__45_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proj R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__46 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__46_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ctor R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__47 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__47_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "scalar "};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__48 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__48_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "retcall #"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__49 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__49_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "call #"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__50 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__50_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ret R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__51 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__51_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "move R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__52 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__52_value;
static const lean_string_object l_Lean_Compiler_Bytecode_Instruction_toString___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "uconst R"};
static const lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___closed__53 = (const lean_object*)&l_Lean_Compiler_Bytecode_Instruction_toString___closed__53_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_toString(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___boxed(lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_Bytecode_disassemble___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Declaration "};
static const lean_object* l_Lean_Compiler_Bytecode_disassemble___closed__0 = (const lean_object*)&l_Lean_Compiler_Bytecode_disassemble___closed__0_value;
static const lean_string_object l_Lean_Compiler_Bytecode_disassemble___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " (arity "};
static const lean_object* l_Lean_Compiler_Bytecode_disassemble___closed__1 = (const lean_object*)&l_Lean_Compiler_Bytecode_disassemble___closed__1_value;
static const lean_string_object l_Lean_Compiler_Bytecode_disassemble___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ") with "};
static const lean_object* l_Lean_Compiler_Bytecode_disassemble___closed__2 = (const lean_object*)&l_Lean_Compiler_Bytecode_disassemble___closed__2_value;
static const lean_string_object l_Lean_Compiler_Bytecode_disassemble___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " stack and "};
static const lean_object* l_Lean_Compiler_Bytecode_disassemble___closed__3 = (const lean_object*)&l_Lean_Compiler_Bytecode_disassemble___closed__3_value;
static const lean_string_object l_Lean_Compiler_Bytecode_disassemble___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " reserved\n"};
static const lean_object* l_Lean_Compiler_Bytecode_disassemble___closed__4 = (const lean_object*)&l_Lean_Compiler_Bytecode_disassemble___closed__4_value;
static const lean_string_object l_Lean_Compiler_Bytecode_disassemble___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Code:\n"};
static const lean_object* l_Lean_Compiler_Bytecode_disassemble___closed__5 = (const lean_object*)&l_Lean_Compiler_Bytecode_disassemble___closed__5_value;
static const lean_string_object l_Lean_Compiler_Bytecode_disassemble___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Symbol table:\n"};
static const lean_object* l_Lean_Compiler_Bytecode_disassemble___closed__6 = (const lean_object*)&l_Lean_Compiler_Bytecode_disassemble___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_disassemble(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint32_t _init_l_Lean_Compiler_Bytecode_instInhabitedInstruction_default(void){
_start:
{
uint32_t v___x_1_; 
v___x_1_ = 0;
return v___x_1_;
}
}
static uint32_t _init_l_Lean_Compiler_Bytecode_instInhabitedInstruction(void){
_start:
{
uint32_t v___x_2_; 
v___x_2_ = 0;
return v___x_2_;
}
}
static lean_object* _init_l_Lean_Compiler_Bytecode_maxUConst(void){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(262143u);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_Compiler_Bytecode_maxNConst(void){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(131071u);
return v___x_4_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_uconst(uint32_t v_target_5_, uint32_t v_val_6_){
_start:
{
uint32_t v___x_7_; uint32_t v___x_8_; uint32_t v___x_9_; 
v___x_7_ = 18;
v___x_8_ = lean_uint32_shift_left(v_target_5_, v___x_7_);
v___x_9_ = lean_uint32_lor(v___x_8_, v_val_6_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_uconst___boxed(lean_object* v_target_10_, lean_object* v_val_11_){
_start:
{
uint32_t v_target_boxed_12_; uint32_t v_val_boxed_13_; uint32_t v_res_14_; lean_object* v_r_15_; 
v_target_boxed_12_ = lean_unbox_uint32(v_target_10_);
lean_dec(v_target_10_);
v_val_boxed_13_ = lean_unbox_uint32(v_val_11_);
lean_dec(v_val_11_);
v_res_14_ = l_Lean_Compiler_Bytecode_Instruction_uconst(v_target_boxed_12_, v_val_boxed_13_);
v_r_15_ = lean_box_uint32(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_nconst(uint32_t v_target_16_, uint32_t v_val_17_){
_start:
{
uint32_t v___x_18_; uint32_t v___x_19_; uint32_t v___x_20_; uint32_t v___x_21_; 
v___x_18_ = 1;
v___x_19_ = lean_uint32_shift_left(v_val_17_, v___x_18_);
v___x_20_ = lean_uint32_lor(v___x_19_, v___x_18_);
v___x_21_ = l_Lean_Compiler_Bytecode_Instruction_uconst(v_target_16_, v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_nconst___boxed(lean_object* v_target_22_, lean_object* v_val_23_){
_start:
{
uint32_t v_target_boxed_24_; uint32_t v_val_boxed_25_; uint32_t v_res_26_; lean_object* v_r_27_; 
v_target_boxed_24_ = lean_unbox_uint32(v_target_22_);
lean_dec(v_target_22_);
v_val_boxed_25_ = lean_unbox_uint32(v_val_23_);
lean_dec(v_val_23_);
v_res_26_ = l_Lean_Compiler_Bytecode_Instruction_nconst(v_target_boxed_24_, v_val_boxed_25_);
v_r_27_ = lean_box_uint32(v_res_26_);
return v_r_27_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_move(uint32_t v_target_28_, uint32_t v_source_29_){
_start:
{
uint32_t v___x_30_; uint32_t v___x_31_; uint32_t v___x_32_; uint32_t v___x_33_; uint32_t v___x_34_; 
v___x_30_ = 67108864;
v___x_31_ = 13;
v___x_32_ = lean_uint32_shift_left(v_target_28_, v___x_31_);
v___x_33_ = lean_uint32_lor(v___x_30_, v___x_32_);
v___x_34_ = lean_uint32_lor(v___x_33_, v_source_29_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_move___boxed(lean_object* v_target_35_, lean_object* v_source_36_){
_start:
{
uint32_t v_target_boxed_37_; uint32_t v_source_boxed_38_; uint32_t v_res_39_; lean_object* v_r_40_; 
v_target_boxed_37_ = lean_unbox_uint32(v_target_35_);
lean_dec(v_target_35_);
v_source_boxed_38_ = lean_unbox_uint32(v_source_36_);
lean_dec(v_source_36_);
v_res_39_ = l_Lean_Compiler_Bytecode_Instruction_move(v_target_boxed_37_, v_source_boxed_38_);
v_r_40_ = lean_box_uint32(v_res_39_);
return v_r_40_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_ret(uint32_t v_target_41_){
_start:
{
uint32_t v___x_42_; uint32_t v___x_43_; 
v___x_42_ = 134217728;
v___x_43_ = lean_uint32_lor(v___x_42_, v_target_41_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_ret___boxed(lean_object* v_target_44_){
_start:
{
uint32_t v_target_boxed_45_; uint32_t v_res_46_; lean_object* v_r_47_; 
v_target_boxed_45_ = lean_unbox_uint32(v_target_44_);
lean_dec(v_target_44_);
v_res_46_ = l_Lean_Compiler_Bytecode_Instruction_ret(v_target_boxed_45_);
v_r_47_ = lean_box_uint32(v_res_46_);
return v_r_47_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_call(uint32_t v_fn_48_){
_start:
{
uint32_t v___x_49_; uint32_t v___x_50_; 
v___x_49_ = 201326592;
v___x_50_ = lean_uint32_lor(v___x_49_, v_fn_48_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_call___boxed(lean_object* v_fn_51_){
_start:
{
uint32_t v_fn_boxed_52_; uint32_t v_res_53_; lean_object* v_r_54_; 
v_fn_boxed_52_ = lean_unbox_uint32(v_fn_51_);
lean_dec(v_fn_51_);
v_res_53_ = l_Lean_Compiler_Bytecode_Instruction_call(v_fn_boxed_52_);
v_r_54_ = lean_box_uint32(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_retcall(uint32_t v_fn_55_){
_start:
{
uint32_t v___x_56_; uint32_t v___x_57_; 
v___x_56_ = 268435456;
v___x_57_ = lean_uint32_lor(v___x_56_, v_fn_55_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_retcall___boxed(lean_object* v_fn_58_){
_start:
{
uint32_t v_fn_boxed_59_; uint32_t v_res_60_; lean_object* v_r_61_; 
v_fn_boxed_59_ = lean_unbox_uint32(v_fn_58_);
lean_dec(v_fn_58_);
v_res_60_ = l_Lean_Compiler_Bytecode_Instruction_retcall(v_fn_boxed_59_);
v_r_61_ = lean_box_uint32(v_res_60_);
return v_r_61_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_computeScalar(uint32_t v_usize_62_, uint32_t v_ssize_63_){
_start:
{
uint32_t v___x_64_; uint32_t v___x_65_; uint32_t v___x_66_; uint32_t v___x_67_; uint32_t v___x_68_; 
v___x_64_ = 335544320;
v___x_65_ = 13;
v___x_66_ = lean_uint32_shift_left(v_usize_62_, v___x_65_);
v___x_67_ = lean_uint32_lor(v___x_64_, v___x_66_);
v___x_68_ = lean_uint32_lor(v___x_67_, v_ssize_63_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_computeScalar___boxed(lean_object* v_usize_69_, lean_object* v_ssize_70_){
_start:
{
uint32_t v_usize_boxed_71_; uint32_t v_ssize_boxed_72_; uint32_t v_res_73_; lean_object* v_r_74_; 
v_usize_boxed_71_ = lean_unbox_uint32(v_usize_69_);
lean_dec(v_usize_69_);
v_ssize_boxed_72_ = lean_unbox_uint32(v_ssize_70_);
lean_dec(v_ssize_70_);
v_res_73_ = l_Lean_Compiler_Bytecode_Instruction_computeScalar(v_usize_boxed_71_, v_ssize_boxed_72_);
v_r_74_ = lean_box_uint32(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_allocCtor(uint32_t v_target_75_, uint32_t v_tag_76_, uint32_t v_numObjs_77_){
_start:
{
uint32_t v___x_78_; uint32_t v___x_79_; uint32_t v___x_80_; uint32_t v___x_81_; uint32_t v___x_82_; uint32_t v___x_83_; uint32_t v___x_84_; uint32_t v___x_85_; 
v___x_78_ = 402653184;
v___x_79_ = 18;
v___x_80_ = lean_uint32_shift_left(v_target_75_, v___x_79_);
v___x_81_ = lean_uint32_lor(v___x_78_, v___x_80_);
v___x_82_ = 8;
v___x_83_ = lean_uint32_shift_left(v_tag_76_, v___x_82_);
v___x_84_ = lean_uint32_lor(v___x_81_, v___x_83_);
v___x_85_ = lean_uint32_lor(v___x_84_, v_numObjs_77_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_allocCtor___boxed(lean_object* v_target_86_, lean_object* v_tag_87_, lean_object* v_numObjs_88_){
_start:
{
uint32_t v_target_boxed_89_; uint32_t v_tag_boxed_90_; uint32_t v_numObjs_boxed_91_; uint32_t v_res_92_; lean_object* v_r_93_; 
v_target_boxed_89_ = lean_unbox_uint32(v_target_86_);
lean_dec(v_target_86_);
v_tag_boxed_90_ = lean_unbox_uint32(v_tag_87_);
lean_dec(v_tag_87_);
v_numObjs_boxed_91_ = lean_unbox_uint32(v_numObjs_88_);
lean_dec(v_numObjs_88_);
v_res_92_ = l_Lean_Compiler_Bytecode_Instruction_allocCtor(v_target_boxed_89_, v_tag_boxed_90_, v_numObjs_boxed_91_);
v_r_93_ = lean_box_uint32(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_proj(uint32_t v_target_94_, uint32_t v_source_95_, uint32_t v_idx_96_){
_start:
{
uint32_t v___x_97_; uint32_t v___x_98_; uint32_t v___x_99_; uint32_t v___x_100_; uint32_t v___x_101_; uint32_t v___x_102_; uint32_t v___x_103_; uint32_t v___x_104_; 
v___x_97_ = 469762048;
v___x_98_ = 16;
v___x_99_ = lean_uint32_shift_left(v_target_94_, v___x_98_);
v___x_100_ = lean_uint32_lor(v___x_97_, v___x_99_);
v___x_101_ = 8;
v___x_102_ = lean_uint32_shift_left(v_source_95_, v___x_101_);
v___x_103_ = lean_uint32_lor(v___x_100_, v___x_102_);
v___x_104_ = lean_uint32_lor(v___x_103_, v_idx_96_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_proj___boxed(lean_object* v_target_105_, lean_object* v_source_106_, lean_object* v_idx_107_){
_start:
{
uint32_t v_target_boxed_108_; uint32_t v_source_boxed_109_; uint32_t v_idx_boxed_110_; uint32_t v_res_111_; lean_object* v_r_112_; 
v_target_boxed_108_ = lean_unbox_uint32(v_target_105_);
lean_dec(v_target_105_);
v_source_boxed_109_ = lean_unbox_uint32(v_source_106_);
lean_dec(v_source_106_);
v_idx_boxed_110_ = lean_unbox_uint32(v_idx_107_);
lean_dec(v_idx_107_);
v_res_111_ = l_Lean_Compiler_Bytecode_Instruction_proj(v_target_boxed_108_, v_source_boxed_109_, v_idx_boxed_110_);
v_r_112_ = lean_box_uint32(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_uproj(uint32_t v_target_113_, uint32_t v_source_114_, uint32_t v_idx_115_){
_start:
{
uint32_t v___x_116_; uint32_t v___x_117_; uint32_t v___x_118_; uint32_t v___x_119_; uint32_t v___x_120_; uint32_t v___x_121_; uint32_t v___x_122_; uint32_t v___x_123_; 
v___x_116_ = 8;
v___x_117_ = 536870912;
v___x_118_ = 16;
v___x_119_ = lean_uint32_shift_left(v_target_113_, v___x_118_);
v___x_120_ = lean_uint32_lor(v___x_117_, v___x_119_);
v___x_121_ = lean_uint32_shift_left(v_source_114_, v___x_116_);
v___x_122_ = lean_uint32_lor(v___x_120_, v___x_121_);
v___x_123_ = lean_uint32_lor(v___x_122_, v_idx_115_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_uproj___boxed(lean_object* v_target_124_, lean_object* v_source_125_, lean_object* v_idx_126_){
_start:
{
uint32_t v_target_boxed_127_; uint32_t v_source_boxed_128_; uint32_t v_idx_boxed_129_; uint32_t v_res_130_; lean_object* v_r_131_; 
v_target_boxed_127_ = lean_unbox_uint32(v_target_124_);
lean_dec(v_target_124_);
v_source_boxed_128_ = lean_unbox_uint32(v_source_125_);
lean_dec(v_source_125_);
v_idx_boxed_129_ = lean_unbox_uint32(v_idx_126_);
lean_dec(v_idx_126_);
v_res_130_ = l_Lean_Compiler_Bytecode_Instruction_uproj(v_target_boxed_127_, v_source_boxed_128_, v_idx_boxed_129_);
v_r_131_ = lean_box_uint32(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_sproj8(uint32_t v_target_132_, uint32_t v_source_133_){
_start:
{
uint32_t v___x_134_; uint32_t v___x_135_; uint32_t v___x_136_; uint32_t v___x_137_; uint32_t v___x_138_; 
v___x_134_ = 603979776;
v___x_135_ = 8;
v___x_136_ = lean_uint32_shift_left(v_target_132_, v___x_135_);
v___x_137_ = lean_uint32_lor(v___x_134_, v___x_136_);
v___x_138_ = lean_uint32_lor(v___x_137_, v_source_133_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sproj8___boxed(lean_object* v_target_139_, lean_object* v_source_140_){
_start:
{
uint32_t v_target_boxed_141_; uint32_t v_source_boxed_142_; uint32_t v_res_143_; lean_object* v_r_144_; 
v_target_boxed_141_ = lean_unbox_uint32(v_target_139_);
lean_dec(v_target_139_);
v_source_boxed_142_ = lean_unbox_uint32(v_source_140_);
lean_dec(v_source_140_);
v_res_143_ = l_Lean_Compiler_Bytecode_Instruction_sproj8(v_target_boxed_141_, v_source_boxed_142_);
v_r_144_ = lean_box_uint32(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_sproj16(uint32_t v_target_145_, uint32_t v_source_146_){
_start:
{
uint32_t v___x_147_; uint32_t v___x_148_; uint32_t v___x_149_; uint32_t v___x_150_; uint32_t v___x_151_; 
v___x_147_ = 671088640;
v___x_148_ = 8;
v___x_149_ = lean_uint32_shift_left(v_target_145_, v___x_148_);
v___x_150_ = lean_uint32_lor(v___x_147_, v___x_149_);
v___x_151_ = lean_uint32_lor(v___x_150_, v_source_146_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sproj16___boxed(lean_object* v_target_152_, lean_object* v_source_153_){
_start:
{
uint32_t v_target_boxed_154_; uint32_t v_source_boxed_155_; uint32_t v_res_156_; lean_object* v_r_157_; 
v_target_boxed_154_ = lean_unbox_uint32(v_target_152_);
lean_dec(v_target_152_);
v_source_boxed_155_ = lean_unbox_uint32(v_source_153_);
lean_dec(v_source_153_);
v_res_156_ = l_Lean_Compiler_Bytecode_Instruction_sproj16(v_target_boxed_154_, v_source_boxed_155_);
v_r_157_ = lean_box_uint32(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_sproj32(uint32_t v_target_158_, uint32_t v_source_159_){
_start:
{
uint32_t v___x_160_; uint32_t v___x_161_; uint32_t v___x_162_; uint32_t v___x_163_; uint32_t v___x_164_; 
v___x_160_ = 738197504;
v___x_161_ = 8;
v___x_162_ = lean_uint32_shift_left(v_target_158_, v___x_161_);
v___x_163_ = lean_uint32_lor(v___x_160_, v___x_162_);
v___x_164_ = lean_uint32_lor(v___x_163_, v_source_159_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sproj32___boxed(lean_object* v_target_165_, lean_object* v_source_166_){
_start:
{
uint32_t v_target_boxed_167_; uint32_t v_source_boxed_168_; uint32_t v_res_169_; lean_object* v_r_170_; 
v_target_boxed_167_ = lean_unbox_uint32(v_target_165_);
lean_dec(v_target_165_);
v_source_boxed_168_ = lean_unbox_uint32(v_source_166_);
lean_dec(v_source_166_);
v_res_169_ = l_Lean_Compiler_Bytecode_Instruction_sproj32(v_target_boxed_167_, v_source_boxed_168_);
v_r_170_ = lean_box_uint32(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_sproj64(uint32_t v_target_171_, uint32_t v_source_172_){
_start:
{
uint32_t v___x_173_; uint32_t v___x_174_; uint32_t v___x_175_; uint32_t v___x_176_; uint32_t v___x_177_; 
v___x_173_ = 805306368;
v___x_174_ = 8;
v___x_175_ = lean_uint32_shift_left(v_target_171_, v___x_174_);
v___x_176_ = lean_uint32_lor(v___x_173_, v___x_175_);
v___x_177_ = lean_uint32_lor(v___x_176_, v_source_172_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sproj64___boxed(lean_object* v_target_178_, lean_object* v_source_179_){
_start:
{
uint32_t v_target_boxed_180_; uint32_t v_source_boxed_181_; uint32_t v_res_182_; lean_object* v_r_183_; 
v_target_boxed_180_ = lean_unbox_uint32(v_target_178_);
lean_dec(v_target_178_);
v_source_boxed_181_ = lean_unbox_uint32(v_source_179_);
lean_dec(v_source_179_);
v_res_182_ = l_Lean_Compiler_Bytecode_Instruction_sproj64(v_target_boxed_180_, v_source_boxed_181_);
v_r_183_ = lean_box_uint32(v_res_182_);
return v_r_183_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_set(uint32_t v_target_184_, uint32_t v_source_185_, uint32_t v_idx_186_){
_start:
{
uint32_t v___x_187_; uint32_t v___x_188_; uint32_t v___x_189_; uint32_t v___x_190_; uint32_t v___x_191_; uint32_t v___x_192_; uint32_t v___x_193_; uint32_t v___x_194_; 
v___x_187_ = 872415232;
v___x_188_ = 16;
v___x_189_ = lean_uint32_shift_left(v_target_184_, v___x_188_);
v___x_190_ = lean_uint32_lor(v___x_187_, v___x_189_);
v___x_191_ = 8;
v___x_192_ = lean_uint32_shift_left(v_source_185_, v___x_191_);
v___x_193_ = lean_uint32_lor(v___x_190_, v___x_192_);
v___x_194_ = lean_uint32_lor(v___x_193_, v_idx_186_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_set___boxed(lean_object* v_target_195_, lean_object* v_source_196_, lean_object* v_idx_197_){
_start:
{
uint32_t v_target_boxed_198_; uint32_t v_source_boxed_199_; uint32_t v_idx_boxed_200_; uint32_t v_res_201_; lean_object* v_r_202_; 
v_target_boxed_198_ = lean_unbox_uint32(v_target_195_);
lean_dec(v_target_195_);
v_source_boxed_199_ = lean_unbox_uint32(v_source_196_);
lean_dec(v_source_196_);
v_idx_boxed_200_ = lean_unbox_uint32(v_idx_197_);
lean_dec(v_idx_197_);
v_res_201_ = l_Lean_Compiler_Bytecode_Instruction_set(v_target_boxed_198_, v_source_boxed_199_, v_idx_boxed_200_);
v_r_202_ = lean_box_uint32(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_uset(uint32_t v_target_203_, uint32_t v_source_204_, uint32_t v_idx_205_){
_start:
{
uint32_t v___x_206_; uint32_t v___x_207_; uint32_t v___x_208_; uint32_t v___x_209_; uint32_t v___x_210_; uint32_t v___x_211_; uint32_t v___x_212_; uint32_t v___x_213_; 
v___x_206_ = 939524096;
v___x_207_ = 16;
v___x_208_ = lean_uint32_shift_left(v_target_203_, v___x_207_);
v___x_209_ = lean_uint32_lor(v___x_206_, v___x_208_);
v___x_210_ = 8;
v___x_211_ = lean_uint32_shift_left(v_source_204_, v___x_210_);
v___x_212_ = lean_uint32_lor(v___x_209_, v___x_211_);
v___x_213_ = lean_uint32_lor(v___x_212_, v_idx_205_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_uset___boxed(lean_object* v_target_214_, lean_object* v_source_215_, lean_object* v_idx_216_){
_start:
{
uint32_t v_target_boxed_217_; uint32_t v_source_boxed_218_; uint32_t v_idx_boxed_219_; uint32_t v_res_220_; lean_object* v_r_221_; 
v_target_boxed_217_ = lean_unbox_uint32(v_target_214_);
lean_dec(v_target_214_);
v_source_boxed_218_ = lean_unbox_uint32(v_source_215_);
lean_dec(v_source_215_);
v_idx_boxed_219_ = lean_unbox_uint32(v_idx_216_);
lean_dec(v_idx_216_);
v_res_220_ = l_Lean_Compiler_Bytecode_Instruction_uset(v_target_boxed_217_, v_source_boxed_218_, v_idx_boxed_219_);
v_r_221_ = lean_box_uint32(v_res_220_);
return v_r_221_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_sset8(uint32_t v_target_222_, uint32_t v_source_223_){
_start:
{
uint32_t v___x_224_; uint32_t v___x_225_; uint32_t v___x_226_; uint32_t v___x_227_; uint32_t v___x_228_; 
v___x_224_ = 1006632960;
v___x_225_ = 8;
v___x_226_ = lean_uint32_shift_left(v_target_222_, v___x_225_);
v___x_227_ = lean_uint32_lor(v___x_224_, v___x_226_);
v___x_228_ = lean_uint32_lor(v___x_227_, v_source_223_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sset8___boxed(lean_object* v_target_229_, lean_object* v_source_230_){
_start:
{
uint32_t v_target_boxed_231_; uint32_t v_source_boxed_232_; uint32_t v_res_233_; lean_object* v_r_234_; 
v_target_boxed_231_ = lean_unbox_uint32(v_target_229_);
lean_dec(v_target_229_);
v_source_boxed_232_ = lean_unbox_uint32(v_source_230_);
lean_dec(v_source_230_);
v_res_233_ = l_Lean_Compiler_Bytecode_Instruction_sset8(v_target_boxed_231_, v_source_boxed_232_);
v_r_234_ = lean_box_uint32(v_res_233_);
return v_r_234_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_sset16(uint32_t v_target_235_, uint32_t v_source_236_){
_start:
{
uint32_t v___x_237_; uint32_t v___x_238_; uint32_t v___x_239_; uint32_t v___x_240_; uint32_t v___x_241_; 
v___x_237_ = 1073741824;
v___x_238_ = 8;
v___x_239_ = lean_uint32_shift_left(v_target_235_, v___x_238_);
v___x_240_ = lean_uint32_lor(v___x_237_, v___x_239_);
v___x_241_ = lean_uint32_lor(v___x_240_, v_source_236_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sset16___boxed(lean_object* v_target_242_, lean_object* v_source_243_){
_start:
{
uint32_t v_target_boxed_244_; uint32_t v_source_boxed_245_; uint32_t v_res_246_; lean_object* v_r_247_; 
v_target_boxed_244_ = lean_unbox_uint32(v_target_242_);
lean_dec(v_target_242_);
v_source_boxed_245_ = lean_unbox_uint32(v_source_243_);
lean_dec(v_source_243_);
v_res_246_ = l_Lean_Compiler_Bytecode_Instruction_sset16(v_target_boxed_244_, v_source_boxed_245_);
v_r_247_ = lean_box_uint32(v_res_246_);
return v_r_247_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_sset32(uint32_t v_target_248_, uint32_t v_source_249_){
_start:
{
uint32_t v___x_250_; uint32_t v___x_251_; uint32_t v___x_252_; uint32_t v___x_253_; uint32_t v___x_254_; 
v___x_250_ = 1140850688;
v___x_251_ = 8;
v___x_252_ = lean_uint32_shift_left(v_target_248_, v___x_251_);
v___x_253_ = lean_uint32_lor(v___x_250_, v___x_252_);
v___x_254_ = lean_uint32_lor(v___x_253_, v_source_249_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sset32___boxed(lean_object* v_target_255_, lean_object* v_source_256_){
_start:
{
uint32_t v_target_boxed_257_; uint32_t v_source_boxed_258_; uint32_t v_res_259_; lean_object* v_r_260_; 
v_target_boxed_257_ = lean_unbox_uint32(v_target_255_);
lean_dec(v_target_255_);
v_source_boxed_258_ = lean_unbox_uint32(v_source_256_);
lean_dec(v_source_256_);
v_res_259_ = l_Lean_Compiler_Bytecode_Instruction_sset32(v_target_boxed_257_, v_source_boxed_258_);
v_r_260_ = lean_box_uint32(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_sset64(uint32_t v_target_261_, uint32_t v_source_262_){
_start:
{
uint32_t v___x_263_; uint32_t v___x_264_; uint32_t v___x_265_; uint32_t v___x_266_; uint32_t v___x_267_; 
v___x_263_ = 1207959552;
v___x_264_ = 8;
v___x_265_ = lean_uint32_shift_left(v_target_261_, v___x_264_);
v___x_266_ = lean_uint32_lor(v___x_263_, v___x_265_);
v___x_267_ = lean_uint32_lor(v___x_266_, v_source_262_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_sset64___boxed(lean_object* v_target_268_, lean_object* v_source_269_){
_start:
{
uint32_t v_target_boxed_270_; uint32_t v_source_boxed_271_; uint32_t v_res_272_; lean_object* v_r_273_; 
v_target_boxed_270_ = lean_unbox_uint32(v_target_268_);
lean_dec(v_target_268_);
v_source_boxed_271_ = lean_unbox_uint32(v_source_269_);
lean_dec(v_source_269_);
v_res_272_ = l_Lean_Compiler_Bytecode_Instruction_sset64(v_target_boxed_270_, v_source_boxed_271_);
v_r_273_ = lean_box_uint32(v_res_272_);
return v_r_273_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_boxSmall(uint32_t v_target_274_, uint32_t v_source_275_){
_start:
{
uint32_t v___x_276_; uint32_t v___x_277_; uint32_t v___x_278_; uint32_t v___x_279_; uint32_t v___x_280_; 
v___x_276_ = 1275068416;
v___x_277_ = 8;
v___x_278_ = lean_uint32_shift_left(v_target_274_, v___x_277_);
v___x_279_ = lean_uint32_lor(v___x_276_, v___x_278_);
v___x_280_ = lean_uint32_lor(v___x_279_, v_source_275_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_boxSmall___boxed(lean_object* v_target_281_, lean_object* v_source_282_){
_start:
{
uint32_t v_target_boxed_283_; uint32_t v_source_boxed_284_; uint32_t v_res_285_; lean_object* v_r_286_; 
v_target_boxed_283_ = lean_unbox_uint32(v_target_281_);
lean_dec(v_target_281_);
v_source_boxed_284_ = lean_unbox_uint32(v_source_282_);
lean_dec(v_source_282_);
v_res_285_ = l_Lean_Compiler_Bytecode_Instruction_boxSmall(v_target_boxed_283_, v_source_boxed_284_);
v_r_286_ = lean_box_uint32(v_res_285_);
return v_r_286_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_boxUInt32(uint32_t v_target_287_, uint32_t v_source_288_){
_start:
{
uint32_t v___x_289_; uint32_t v___x_290_; uint32_t v___x_291_; uint32_t v___x_292_; uint32_t v___x_293_; 
v___x_289_ = 1342177280;
v___x_290_ = 8;
v___x_291_ = lean_uint32_shift_left(v_target_287_, v___x_290_);
v___x_292_ = lean_uint32_lor(v___x_289_, v___x_291_);
v___x_293_ = lean_uint32_lor(v___x_292_, v_source_288_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_boxUInt32___boxed(lean_object* v_target_294_, lean_object* v_source_295_){
_start:
{
uint32_t v_target_boxed_296_; uint32_t v_source_boxed_297_; uint32_t v_res_298_; lean_object* v_r_299_; 
v_target_boxed_296_ = lean_unbox_uint32(v_target_294_);
lean_dec(v_target_294_);
v_source_boxed_297_ = lean_unbox_uint32(v_source_295_);
lean_dec(v_source_295_);
v_res_298_ = l_Lean_Compiler_Bytecode_Instruction_boxUInt32(v_target_boxed_296_, v_source_boxed_297_);
v_r_299_ = lean_box_uint32(v_res_298_);
return v_r_299_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_boxUInt64(uint32_t v_target_300_, uint32_t v_source_301_){
_start:
{
uint32_t v___x_302_; uint32_t v___x_303_; uint32_t v___x_304_; uint32_t v___x_305_; uint32_t v___x_306_; 
v___x_302_ = 1409286144;
v___x_303_ = 8;
v___x_304_ = lean_uint32_shift_left(v_target_300_, v___x_303_);
v___x_305_ = lean_uint32_lor(v___x_302_, v___x_304_);
v___x_306_ = lean_uint32_lor(v___x_305_, v_source_301_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_boxUInt64___boxed(lean_object* v_target_307_, lean_object* v_source_308_){
_start:
{
uint32_t v_target_boxed_309_; uint32_t v_source_boxed_310_; uint32_t v_res_311_; lean_object* v_r_312_; 
v_target_boxed_309_ = lean_unbox_uint32(v_target_307_);
lean_dec(v_target_307_);
v_source_boxed_310_ = lean_unbox_uint32(v_source_308_);
lean_dec(v_source_308_);
v_res_311_ = l_Lean_Compiler_Bytecode_Instruction_boxUInt64(v_target_boxed_309_, v_source_boxed_310_);
v_r_312_ = lean_box_uint32(v_res_311_);
return v_r_312_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_boxUSize(uint32_t v_target_313_, uint32_t v_source_314_){
_start:
{
uint32_t v___x_315_; uint32_t v___x_316_; uint32_t v___x_317_; uint32_t v___x_318_; uint32_t v___x_319_; 
v___x_315_ = 1476395008;
v___x_316_ = 8;
v___x_317_ = lean_uint32_shift_left(v_target_313_, v___x_316_);
v___x_318_ = lean_uint32_lor(v___x_315_, v___x_317_);
v___x_319_ = lean_uint32_lor(v___x_318_, v_source_314_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_boxUSize___boxed(lean_object* v_target_320_, lean_object* v_source_321_){
_start:
{
uint32_t v_target_boxed_322_; uint32_t v_source_boxed_323_; uint32_t v_res_324_; lean_object* v_r_325_; 
v_target_boxed_322_ = lean_unbox_uint32(v_target_320_);
lean_dec(v_target_320_);
v_source_boxed_323_ = lean_unbox_uint32(v_source_321_);
lean_dec(v_source_321_);
v_res_324_ = l_Lean_Compiler_Bytecode_Instruction_boxUSize(v_target_boxed_322_, v_source_boxed_323_);
v_r_325_ = lean_box_uint32(v_res_324_);
return v_r_325_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_boxFloat(uint32_t v_target_326_, uint32_t v_source_327_){
_start:
{
uint32_t v___x_328_; uint32_t v___x_329_; uint32_t v___x_330_; uint32_t v___x_331_; uint32_t v___x_332_; 
v___x_328_ = 1543503872;
v___x_329_ = 8;
v___x_330_ = lean_uint32_shift_left(v_target_326_, v___x_329_);
v___x_331_ = lean_uint32_lor(v___x_328_, v___x_330_);
v___x_332_ = lean_uint32_lor(v___x_331_, v_source_327_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_boxFloat___boxed(lean_object* v_target_333_, lean_object* v_source_334_){
_start:
{
uint32_t v_target_boxed_335_; uint32_t v_source_boxed_336_; uint32_t v_res_337_; lean_object* v_r_338_; 
v_target_boxed_335_ = lean_unbox_uint32(v_target_333_);
lean_dec(v_target_333_);
v_source_boxed_336_ = lean_unbox_uint32(v_source_334_);
lean_dec(v_source_334_);
v_res_337_ = l_Lean_Compiler_Bytecode_Instruction_boxFloat(v_target_boxed_335_, v_source_boxed_336_);
v_r_338_ = lean_box_uint32(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_boxFloat32(uint32_t v_target_339_, uint32_t v_source_340_){
_start:
{
uint32_t v___x_341_; uint32_t v___x_342_; uint32_t v___x_343_; uint32_t v___x_344_; uint32_t v___x_345_; 
v___x_341_ = 1610612736;
v___x_342_ = 8;
v___x_343_ = lean_uint32_shift_left(v_target_339_, v___x_342_);
v___x_344_ = lean_uint32_lor(v___x_341_, v___x_343_);
v___x_345_ = lean_uint32_lor(v___x_344_, v_source_340_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_boxFloat32___boxed(lean_object* v_target_346_, lean_object* v_source_347_){
_start:
{
uint32_t v_target_boxed_348_; uint32_t v_source_boxed_349_; uint32_t v_res_350_; lean_object* v_r_351_; 
v_target_boxed_348_ = lean_unbox_uint32(v_target_346_);
lean_dec(v_target_346_);
v_source_boxed_349_ = lean_unbox_uint32(v_source_347_);
lean_dec(v_source_347_);
v_res_350_ = l_Lean_Compiler_Bytecode_Instruction_boxFloat32(v_target_boxed_348_, v_source_boxed_349_);
v_r_351_ = lean_box_uint32(v_res_350_);
return v_r_351_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_unboxSmall(uint32_t v_target_352_, uint32_t v_source_353_){
_start:
{
uint32_t v___x_354_; uint32_t v___x_355_; uint32_t v___x_356_; uint32_t v___x_357_; uint32_t v___x_358_; 
v___x_354_ = 1677721600;
v___x_355_ = 8;
v___x_356_ = lean_uint32_shift_left(v_target_352_, v___x_355_);
v___x_357_ = lean_uint32_lor(v___x_354_, v___x_356_);
v___x_358_ = lean_uint32_lor(v___x_357_, v_source_353_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_unboxSmall___boxed(lean_object* v_target_359_, lean_object* v_source_360_){
_start:
{
uint32_t v_target_boxed_361_; uint32_t v_source_boxed_362_; uint32_t v_res_363_; lean_object* v_r_364_; 
v_target_boxed_361_ = lean_unbox_uint32(v_target_359_);
lean_dec(v_target_359_);
v_source_boxed_362_ = lean_unbox_uint32(v_source_360_);
lean_dec(v_source_360_);
v_res_363_ = l_Lean_Compiler_Bytecode_Instruction_unboxSmall(v_target_boxed_361_, v_source_boxed_362_);
v_r_364_ = lean_box_uint32(v_res_363_);
return v_r_364_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_unboxUInt32(uint32_t v_target_365_, uint32_t v_source_366_){
_start:
{
uint32_t v___x_367_; uint32_t v___x_368_; uint32_t v___x_369_; uint32_t v___x_370_; uint32_t v___x_371_; 
v___x_367_ = 1744830464;
v___x_368_ = 8;
v___x_369_ = lean_uint32_shift_left(v_target_365_, v___x_368_);
v___x_370_ = lean_uint32_lor(v___x_367_, v___x_369_);
v___x_371_ = lean_uint32_lor(v___x_370_, v_source_366_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_unboxUInt32___boxed(lean_object* v_target_372_, lean_object* v_source_373_){
_start:
{
uint32_t v_target_boxed_374_; uint32_t v_source_boxed_375_; uint32_t v_res_376_; lean_object* v_r_377_; 
v_target_boxed_374_ = lean_unbox_uint32(v_target_372_);
lean_dec(v_target_372_);
v_source_boxed_375_ = lean_unbox_uint32(v_source_373_);
lean_dec(v_source_373_);
v_res_376_ = l_Lean_Compiler_Bytecode_Instruction_unboxUInt32(v_target_boxed_374_, v_source_boxed_375_);
v_r_377_ = lean_box_uint32(v_res_376_);
return v_r_377_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_unboxUInt64(uint32_t v_target_378_, uint32_t v_source_379_){
_start:
{
uint32_t v___x_380_; uint32_t v___x_381_; uint32_t v___x_382_; uint32_t v___x_383_; uint32_t v___x_384_; 
v___x_380_ = 1811939328;
v___x_381_ = 8;
v___x_382_ = lean_uint32_shift_left(v_target_378_, v___x_381_);
v___x_383_ = lean_uint32_lor(v___x_380_, v___x_382_);
v___x_384_ = lean_uint32_lor(v___x_383_, v_source_379_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_unboxUInt64___boxed(lean_object* v_target_385_, lean_object* v_source_386_){
_start:
{
uint32_t v_target_boxed_387_; uint32_t v_source_boxed_388_; uint32_t v_res_389_; lean_object* v_r_390_; 
v_target_boxed_387_ = lean_unbox_uint32(v_target_385_);
lean_dec(v_target_385_);
v_source_boxed_388_ = lean_unbox_uint32(v_source_386_);
lean_dec(v_source_386_);
v_res_389_ = l_Lean_Compiler_Bytecode_Instruction_unboxUInt64(v_target_boxed_387_, v_source_boxed_388_);
v_r_390_ = lean_box_uint32(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_unboxUSize(uint32_t v_target_391_, uint32_t v_source_392_){
_start:
{
uint32_t v___x_393_; uint32_t v___x_394_; uint32_t v___x_395_; uint32_t v___x_396_; uint32_t v___x_397_; 
v___x_393_ = 1879048192;
v___x_394_ = 8;
v___x_395_ = lean_uint32_shift_left(v_target_391_, v___x_394_);
v___x_396_ = lean_uint32_lor(v___x_393_, v___x_395_);
v___x_397_ = lean_uint32_lor(v___x_396_, v_source_392_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_unboxUSize___boxed(lean_object* v_target_398_, lean_object* v_source_399_){
_start:
{
uint32_t v_target_boxed_400_; uint32_t v_source_boxed_401_; uint32_t v_res_402_; lean_object* v_r_403_; 
v_target_boxed_400_ = lean_unbox_uint32(v_target_398_);
lean_dec(v_target_398_);
v_source_boxed_401_ = lean_unbox_uint32(v_source_399_);
lean_dec(v_source_399_);
v_res_402_ = l_Lean_Compiler_Bytecode_Instruction_unboxUSize(v_target_boxed_400_, v_source_boxed_401_);
v_r_403_ = lean_box_uint32(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_unboxFloat(uint32_t v_target_404_, uint32_t v_source_405_){
_start:
{
uint32_t v___x_406_; uint32_t v___x_407_; uint32_t v___x_408_; uint32_t v___x_409_; uint32_t v___x_410_; 
v___x_406_ = 1946157056;
v___x_407_ = 8;
v___x_408_ = lean_uint32_shift_left(v_target_404_, v___x_407_);
v___x_409_ = lean_uint32_lor(v___x_406_, v___x_408_);
v___x_410_ = lean_uint32_lor(v___x_409_, v_source_405_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_unboxFloat___boxed(lean_object* v_target_411_, lean_object* v_source_412_){
_start:
{
uint32_t v_target_boxed_413_; uint32_t v_source_boxed_414_; uint32_t v_res_415_; lean_object* v_r_416_; 
v_target_boxed_413_ = lean_unbox_uint32(v_target_411_);
lean_dec(v_target_411_);
v_source_boxed_414_ = lean_unbox_uint32(v_source_412_);
lean_dec(v_source_412_);
v_res_415_ = l_Lean_Compiler_Bytecode_Instruction_unboxFloat(v_target_boxed_413_, v_source_boxed_414_);
v_r_416_ = lean_box_uint32(v_res_415_);
return v_r_416_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_unboxFloat32(uint32_t v_target_417_, uint32_t v_source_418_){
_start:
{
uint32_t v___x_419_; uint32_t v___x_420_; uint32_t v___x_421_; uint32_t v___x_422_; uint32_t v___x_423_; 
v___x_419_ = 2013265920;
v___x_420_ = 8;
v___x_421_ = lean_uint32_shift_left(v_target_417_, v___x_420_);
v___x_422_ = lean_uint32_lor(v___x_419_, v___x_421_);
v___x_423_ = lean_uint32_lor(v___x_422_, v_source_418_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_unboxFloat32___boxed(lean_object* v_target_424_, lean_object* v_source_425_){
_start:
{
uint32_t v_target_boxed_426_; uint32_t v_source_boxed_427_; uint32_t v_res_428_; lean_object* v_r_429_; 
v_target_boxed_426_ = lean_unbox_uint32(v_target_424_);
lean_dec(v_target_424_);
v_source_boxed_427_ = lean_unbox_uint32(v_source_425_);
lean_dec(v_source_425_);
v_res_428_ = l_Lean_Compiler_Bytecode_Instruction_unboxFloat32(v_target_boxed_426_, v_source_boxed_427_);
v_r_429_ = lean_box_uint32(v_res_428_);
return v_r_429_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_inc(uint32_t v_target_430_, uint32_t v_count_431_){
_start:
{
uint32_t v___x_432_; uint32_t v___x_433_; uint32_t v___x_434_; uint32_t v___x_435_; uint32_t v___x_436_; 
v___x_432_ = 2080374784;
v___x_433_ = 8;
v___x_434_ = lean_uint32_shift_left(v_target_430_, v___x_433_);
v___x_435_ = lean_uint32_lor(v___x_432_, v___x_434_);
v___x_436_ = lean_uint32_lor(v___x_435_, v_count_431_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_inc___boxed(lean_object* v_target_437_, lean_object* v_count_438_){
_start:
{
uint32_t v_target_boxed_439_; uint32_t v_count_boxed_440_; uint32_t v_res_441_; lean_object* v_r_442_; 
v_target_boxed_439_ = lean_unbox_uint32(v_target_437_);
lean_dec(v_target_437_);
v_count_boxed_440_ = lean_unbox_uint32(v_count_438_);
lean_dec(v_count_438_);
v_res_441_ = l_Lean_Compiler_Bytecode_Instruction_inc(v_target_boxed_439_, v_count_boxed_440_);
v_r_442_ = lean_box_uint32(v_res_441_);
return v_r_442_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_dec(uint32_t v_target_443_, uint32_t v_count_444_){
_start:
{
uint32_t v___x_445_; uint32_t v___x_446_; uint32_t v___x_447_; uint32_t v___x_448_; uint32_t v___x_449_; 
v___x_445_ = 2147483648;
v___x_446_ = 8;
v___x_447_ = lean_uint32_shift_left(v_target_443_, v___x_446_);
v___x_448_ = lean_uint32_lor(v___x_445_, v___x_447_);
v___x_449_ = lean_uint32_lor(v___x_448_, v_count_444_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_dec___boxed(lean_object* v_target_450_, lean_object* v_count_451_){
_start:
{
uint32_t v_target_boxed_452_; uint32_t v_count_boxed_453_; uint32_t v_res_454_; lean_object* v_r_455_; 
v_target_boxed_452_ = lean_unbox_uint32(v_target_450_);
lean_dec(v_target_450_);
v_count_boxed_453_ = lean_unbox_uint32(v_count_451_);
lean_dec(v_count_451_);
v_res_454_ = l_Lean_Compiler_Bytecode_Instruction_dec(v_target_boxed_452_, v_count_boxed_453_);
v_r_455_ = lean_box_uint32(v_res_454_);
return v_r_455_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_isShared(uint32_t v_target_456_, uint32_t v_source_457_){
_start:
{
uint32_t v___x_458_; uint32_t v___x_459_; uint32_t v___x_460_; uint32_t v___x_461_; uint32_t v___x_462_; 
v___x_458_ = 2214592512;
v___x_459_ = 8;
v___x_460_ = lean_uint32_shift_left(v_target_456_, v___x_459_);
v___x_461_ = lean_uint32_lor(v___x_458_, v___x_460_);
v___x_462_ = lean_uint32_lor(v___x_461_, v_source_457_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_isShared___boxed(lean_object* v_target_463_, lean_object* v_source_464_){
_start:
{
uint32_t v_target_boxed_465_; uint32_t v_source_boxed_466_; uint32_t v_res_467_; lean_object* v_r_468_; 
v_target_boxed_465_ = lean_unbox_uint32(v_target_463_);
lean_dec(v_target_463_);
v_source_boxed_466_ = lean_unbox_uint32(v_source_464_);
lean_dec(v_source_464_);
v_res_467_ = l_Lean_Compiler_Bytecode_Instruction_isShared(v_target_boxed_465_, v_source_boxed_466_);
v_r_468_ = lean_box_uint32(v_res_467_);
return v_r_468_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_loadTag(uint32_t v_target_469_, uint32_t v_source_470_){
_start:
{
uint32_t v___x_471_; uint32_t v___x_472_; uint32_t v___x_473_; uint32_t v___x_474_; uint32_t v___x_475_; 
v___x_471_ = 2281701376;
v___x_472_ = 8;
v___x_473_ = lean_uint32_shift_left(v_target_469_, v___x_472_);
v___x_474_ = lean_uint32_lor(v___x_471_, v___x_473_);
v___x_475_ = lean_uint32_lor(v___x_474_, v_source_470_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_loadTag___boxed(lean_object* v_target_476_, lean_object* v_source_477_){
_start:
{
uint32_t v_target_boxed_478_; uint32_t v_source_boxed_479_; uint32_t v_res_480_; lean_object* v_r_481_; 
v_target_boxed_478_ = lean_unbox_uint32(v_target_476_);
lean_dec(v_target_476_);
v_source_boxed_479_ = lean_unbox_uint32(v_source_477_);
lean_dec(v_source_477_);
v_res_480_ = l_Lean_Compiler_Bytecode_Instruction_loadTag(v_target_boxed_478_, v_source_boxed_479_);
v_r_481_ = lean_box_uint32(v_res_480_);
return v_r_481_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_jumpTable(uint32_t v_source_482_, uint32_t v_limit_483_){
_start:
{
uint32_t v___x_484_; uint32_t v___x_485_; uint32_t v___x_486_; uint32_t v___x_487_; uint32_t v___x_488_; 
v___x_484_ = 2348810240;
v___x_485_ = 10;
v___x_486_ = lean_uint32_shift_left(v_source_482_, v___x_485_);
v___x_487_ = lean_uint32_lor(v___x_484_, v___x_486_);
v___x_488_ = lean_uint32_lor(v___x_487_, v_limit_483_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_jumpTable___boxed(lean_object* v_source_489_, lean_object* v_limit_490_){
_start:
{
uint32_t v_source_boxed_491_; uint32_t v_limit_boxed_492_; uint32_t v_res_493_; lean_object* v_r_494_; 
v_source_boxed_491_ = lean_unbox_uint32(v_source_489_);
lean_dec(v_source_489_);
v_limit_boxed_492_ = lean_unbox_uint32(v_limit_490_);
lean_dec(v_limit_490_);
v_res_493_ = l_Lean_Compiler_Bytecode_Instruction_jumpTable(v_source_boxed_491_, v_limit_boxed_492_);
v_r_494_ = lean_box_uint32(v_res_493_);
return v_r_494_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_setTag(uint32_t v_target_495_, uint32_t v_tag_496_){
_start:
{
uint32_t v___x_497_; uint32_t v___x_498_; uint32_t v___x_499_; uint32_t v___x_500_; uint32_t v___x_501_; 
v___x_497_ = 2415919104;
v___x_498_ = 10;
v___x_499_ = lean_uint32_shift_left(v_target_495_, v___x_498_);
v___x_500_ = lean_uint32_lor(v___x_497_, v___x_499_);
v___x_501_ = lean_uint32_lor(v___x_500_, v_tag_496_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_setTag___boxed(lean_object* v_target_502_, lean_object* v_tag_503_){
_start:
{
uint32_t v_target_boxed_504_; uint32_t v_tag_boxed_505_; uint32_t v_res_506_; lean_object* v_r_507_; 
v_target_boxed_504_ = lean_unbox_uint32(v_target_502_);
lean_dec(v_target_502_);
v_tag_boxed_505_ = lean_unbox_uint32(v_tag_503_);
lean_dec(v_tag_503_);
v_res_506_ = l_Lean_Compiler_Bytecode_Instruction_setTag(v_target_boxed_504_, v_tag_boxed_505_);
v_r_507_ = lean_box_uint32(v_res_506_);
return v_r_507_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_loadConst(uint32_t v_fn_508_){
_start:
{
uint32_t v___x_509_; uint32_t v___x_510_; 
v___x_509_ = 2483027968;
v___x_510_ = lean_uint32_lor(v___x_509_, v_fn_508_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_loadConst___boxed(lean_object* v_fn_511_){
_start:
{
uint32_t v_fn_boxed_512_; uint32_t v_res_513_; lean_object* v_r_514_; 
v_fn_boxed_512_ = lean_unbox_uint32(v_fn_511_);
lean_dec(v_fn_511_);
v_res_513_ = l_Lean_Compiler_Bytecode_Instruction_loadConst(v_fn_boxed_512_);
v_r_514_ = lean_box_uint32(v_res_513_);
return v_r_514_;
}
}
static uint32_t _init_l_Lean_Compiler_Bytecode_Instruction_ifTag___closed__0(void){
_start:
{
lean_object* v___x_515_; uint32_t v___x_516_; 
v___x_515_ = lean_unsigned_to_nat(128u);
v___x_516_ = lean_int32_of_nat(v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_ifTag(uint32_t v_target_517_, uint32_t v_tag_518_, uint32_t v_offset_519_){
_start:
{
uint32_t v___x_520_; uint32_t v___x_521_; uint32_t v___x_522_; uint32_t v___x_523_; uint32_t v___x_524_; uint32_t v___x_525_; uint32_t v___x_526_; uint32_t v___x_527_; uint32_t v___x_528_; uint32_t v___x_529_; 
v___x_520_ = 2550136832;
v___x_521_ = 18;
v___x_522_ = lean_uint32_shift_left(v_target_517_, v___x_521_);
v___x_523_ = lean_uint32_lor(v___x_520_, v___x_522_);
v___x_524_ = 8;
v___x_525_ = lean_uint32_shift_left(v_tag_518_, v___x_524_);
v___x_526_ = lean_uint32_lor(v___x_523_, v___x_525_);
v___x_527_ = lean_uint32_once(&l_Lean_Compiler_Bytecode_Instruction_ifTag___closed__0, &l_Lean_Compiler_Bytecode_Instruction_ifTag___closed__0_once, _init_l_Lean_Compiler_Bytecode_Instruction_ifTag___closed__0);
v___x_528_ = lean_int32_add(v_offset_519_, v___x_527_);
v___x_529_ = lean_uint32_lor(v___x_526_, v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_ifTag___boxed(lean_object* v_target_530_, lean_object* v_tag_531_, lean_object* v_offset_532_){
_start:
{
uint32_t v_target_boxed_533_; uint32_t v_tag_boxed_534_; uint32_t v_offset_boxed_535_; uint32_t v_res_536_; lean_object* v_r_537_; 
v_target_boxed_533_ = lean_unbox_uint32(v_target_530_);
lean_dec(v_target_530_);
v_tag_boxed_534_ = lean_unbox_uint32(v_tag_531_);
lean_dec(v_tag_531_);
v_offset_boxed_535_ = lean_unbox_uint32(v_offset_532_);
lean_dec(v_offset_532_);
v_res_536_ = l_Lean_Compiler_Bytecode_Instruction_ifTag(v_target_boxed_533_, v_tag_boxed_534_, v_offset_boxed_535_);
v_r_537_ = lean_box_uint32(v_res_536_);
return v_r_537_;
}
}
static uint32_t _init_l_Lean_Compiler_Bytecode_Instruction_jump___closed__0(void){
_start:
{
lean_object* v___x_538_; uint32_t v___x_539_; 
v___x_538_ = lean_unsigned_to_nat(33554432u);
v___x_539_ = lean_int32_of_nat(v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_jump(uint32_t v_offset_540_){
_start:
{
uint32_t v___x_541_; uint32_t v___x_542_; uint32_t v___x_543_; uint32_t v___x_544_; 
v___x_541_ = 2617245696;
v___x_542_ = lean_uint32_once(&l_Lean_Compiler_Bytecode_Instruction_jump___closed__0, &l_Lean_Compiler_Bytecode_Instruction_jump___closed__0_once, _init_l_Lean_Compiler_Bytecode_Instruction_jump___closed__0);
v___x_543_ = lean_int32_add(v_offset_540_, v___x_542_);
v___x_544_ = lean_uint32_lor(v___x_541_, v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_jump___boxed(lean_object* v_offset_545_){
_start:
{
uint32_t v_offset_boxed_546_; uint32_t v_res_547_; lean_object* v_r_548_; 
v_offset_boxed_546_ = lean_unbox_uint32(v_offset_545_);
lean_dec(v_offset_545_);
v_res_547_ = l_Lean_Compiler_Bytecode_Instruction_jump(v_offset_boxed_546_);
v_r_548_ = lean_box_uint32(v_res_547_);
return v_r_548_;
}
}
static uint32_t _init_l_Lean_Compiler_Bytecode_Instruction_nojump(void){
_start:
{
uint32_t v___x_549_; 
v___x_549_ = 2617245696;
return v___x_549_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_app(uint32_t v_fn_550_, uint32_t v_n_551_){
_start:
{
uint32_t v___x_552_; uint32_t v___x_553_; uint32_t v___x_554_; uint32_t v___x_555_; uint32_t v___x_556_; 
v___x_552_ = 2684354560;
v___x_553_ = 16;
v___x_554_ = lean_uint32_shift_left(v_n_551_, v___x_553_);
v___x_555_ = lean_uint32_lor(v___x_552_, v___x_554_);
v___x_556_ = lean_uint32_lor(v___x_555_, v_fn_550_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_app___boxed(lean_object* v_fn_557_, lean_object* v_n_558_){
_start:
{
uint32_t v_fn_boxed_559_; uint32_t v_n_boxed_560_; uint32_t v_res_561_; lean_object* v_r_562_; 
v_fn_boxed_559_ = lean_unbox_uint32(v_fn_557_);
lean_dec(v_fn_557_);
v_n_boxed_560_ = lean_unbox_uint32(v_n_558_);
lean_dec(v_n_558_);
v_res_561_ = l_Lean_Compiler_Bytecode_Instruction_app(v_fn_boxed_559_, v_n_boxed_560_);
v_r_562_ = lean_box_uint32(v_res_561_);
return v_r_562_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_pap(uint32_t v_fn_563_, uint32_t v_n_564_){
_start:
{
uint32_t v___x_565_; uint32_t v___x_566_; uint32_t v___x_567_; uint32_t v___x_568_; uint32_t v___x_569_; 
v___x_565_ = 2751463424;
v___x_566_ = 16;
v___x_567_ = lean_uint32_shift_left(v_n_564_, v___x_566_);
v___x_568_ = lean_uint32_lor(v___x_565_, v___x_567_);
v___x_569_ = lean_uint32_lor(v___x_568_, v_fn_563_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_pap___boxed(lean_object* v_fn_570_, lean_object* v_n_571_){
_start:
{
uint32_t v_fn_boxed_572_; uint32_t v_n_boxed_573_; uint32_t v_res_574_; lean_object* v_r_575_; 
v_fn_boxed_572_ = lean_unbox_uint32(v_fn_570_);
lean_dec(v_fn_570_);
v_n_boxed_573_ = lean_unbox_uint32(v_n_571_);
lean_dec(v_n_571_);
v_res_574_ = l_Lean_Compiler_Bytecode_Instruction_pap(v_fn_boxed_572_, v_n_boxed_573_);
v_r_575_ = lean_box_uint32(v_res_574_);
return v_r_575_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_del(uint32_t v_target_576_){
_start:
{
uint32_t v___x_577_; uint32_t v___x_578_; 
v___x_577_ = 2818572288;
v___x_578_ = lean_uint32_lor(v___x_577_, v_target_576_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_del___boxed(lean_object* v_target_579_){
_start:
{
uint32_t v_target_boxed_580_; uint32_t v_res_581_; lean_object* v_r_582_; 
v_target_boxed_580_ = lean_unbox_uint32(v_target_579_);
lean_dec(v_target_579_);
v_res_581_ = l_Lean_Compiler_Bytecode_Instruction_del(v_target_boxed_580_);
v_r_582_ = lean_box_uint32(v_res_581_);
return v_r_582_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_reset(uint32_t v_n_583_, uint32_t v_target_584_, uint32_t v_source_585_){
_start:
{
uint32_t v___x_586_; uint32_t v___x_587_; uint32_t v___x_588_; uint32_t v___x_589_; uint32_t v___x_590_; uint32_t v___x_591_; uint32_t v___x_592_; uint32_t v___x_593_; 
v___x_586_ = 2885681152;
v___x_587_ = 16;
v___x_588_ = lean_uint32_shift_left(v_n_583_, v___x_587_);
v___x_589_ = lean_uint32_lor(v___x_586_, v___x_588_);
v___x_590_ = 8;
v___x_591_ = lean_uint32_shift_left(v_target_584_, v___x_590_);
v___x_592_ = lean_uint32_lor(v___x_589_, v___x_591_);
v___x_593_ = lean_uint32_lor(v___x_592_, v_source_585_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_reset___boxed(lean_object* v_n_594_, lean_object* v_target_595_, lean_object* v_source_596_){
_start:
{
uint32_t v_n_boxed_597_; uint32_t v_target_boxed_598_; uint32_t v_source_boxed_599_; uint32_t v_res_600_; lean_object* v_r_601_; 
v_n_boxed_597_ = lean_unbox_uint32(v_n_594_);
lean_dec(v_n_594_);
v_target_boxed_598_ = lean_unbox_uint32(v_target_595_);
lean_dec(v_target_595_);
v_source_boxed_599_ = lean_unbox_uint32(v_source_596_);
lean_dec(v_source_596_);
v_res_600_ = l_Lean_Compiler_Bytecode_Instruction_reset(v_n_boxed_597_, v_target_boxed_598_, v_source_boxed_599_);
v_r_601_ = lean_box_uint32(v_res_600_);
return v_r_601_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_reuse(uint32_t v_target_602_, uint32_t v_tag_603_, uint32_t v_numObjs_604_){
_start:
{
uint32_t v___x_605_; uint32_t v___x_606_; uint32_t v___x_607_; uint32_t v___x_608_; uint32_t v___x_609_; uint32_t v___x_610_; uint32_t v___x_611_; uint32_t v___x_612_; 
v___x_605_ = 2952790016;
v___x_606_ = 18;
v___x_607_ = lean_uint32_shift_left(v_target_602_, v___x_606_);
v___x_608_ = lean_uint32_lor(v___x_605_, v___x_607_);
v___x_609_ = 8;
v___x_610_ = lean_uint32_shift_left(v_tag_603_, v___x_609_);
v___x_611_ = lean_uint32_lor(v___x_608_, v___x_610_);
v___x_612_ = lean_uint32_lor(v___x_611_, v_numObjs_604_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_reuse___boxed(lean_object* v_target_613_, lean_object* v_tag_614_, lean_object* v_numObjs_615_){
_start:
{
uint32_t v_target_boxed_616_; uint32_t v_tag_boxed_617_; uint32_t v_numObjs_boxed_618_; uint32_t v_res_619_; lean_object* v_r_620_; 
v_target_boxed_616_ = lean_unbox_uint32(v_target_613_);
lean_dec(v_target_613_);
v_tag_boxed_617_ = lean_unbox_uint32(v_tag_614_);
lean_dec(v_tag_614_);
v_numObjs_boxed_618_ = lean_unbox_uint32(v_numObjs_615_);
lean_dec(v_numObjs_615_);
v_res_619_ = l_Lean_Compiler_Bytecode_Instruction_reuse(v_target_boxed_616_, v_tag_boxed_617_, v_numObjs_boxed_618_);
v_r_620_ = lean_box_uint32(v_res_619_);
return v_r_620_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_storeCache(uint32_t v_target_621_){
_start:
{
uint32_t v___x_622_; uint32_t v___x_623_; 
v___x_622_ = 3019898880;
v___x_623_ = lean_uint32_lor(v___x_622_, v_target_621_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_storeCache___boxed(lean_object* v_target_624_){
_start:
{
uint32_t v_target_boxed_625_; uint32_t v_res_626_; lean_object* v_r_627_; 
v_target_boxed_625_ = lean_unbox_uint32(v_target_624_);
lean_dec(v_target_624_);
v_res_626_ = l_Lean_Compiler_Bytecode_Instruction_storeCache(v_target_boxed_625_);
v_r_627_ = lean_box_uint32(v_res_626_);
return v_r_627_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_skipIfCached(uint32_t v_offset_628_){
_start:
{
uint32_t v___x_629_; uint32_t v___x_630_; 
v___x_629_ = 3087007744;
v___x_630_ = lean_uint32_lor(v___x_629_, v_offset_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_skipIfCached___boxed(lean_object* v_offset_631_){
_start:
{
uint32_t v_offset_boxed_632_; uint32_t v_res_633_; lean_object* v_r_634_; 
v_offset_boxed_632_ = lean_unbox_uint32(v_offset_631_);
lean_dec(v_offset_631_);
v_res_633_ = l_Lean_Compiler_Bytecode_Instruction_skipIfCached(v_offset_boxed_632_);
v_r_634_ = lean_box_uint32(v_res_633_);
return v_r_634_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_declConst(uint32_t v_tgt_635_, uint32_t v_id_636_){
_start:
{
uint32_t v___x_637_; uint32_t v___x_638_; uint32_t v___x_639_; uint32_t v___x_640_; uint32_t v___x_641_; 
v___x_637_ = 3154116608;
v___x_638_ = 18;
v___x_639_ = lean_uint32_shift_left(v_tgt_635_, v___x_638_);
v___x_640_ = lean_uint32_lor(v___x_637_, v___x_639_);
v___x_641_ = lean_uint32_lor(v___x_640_, v_id_636_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_declConst___boxed(lean_object* v_tgt_642_, lean_object* v_id_643_){
_start:
{
uint32_t v_tgt_boxed_644_; uint32_t v_id_boxed_645_; uint32_t v_res_646_; lean_object* v_r_647_; 
v_tgt_boxed_644_ = lean_unbox_uint32(v_tgt_642_);
lean_dec(v_tgt_642_);
v_id_boxed_645_ = lean_unbox_uint32(v_id_643_);
lean_dec(v_id_643_);
v_res_646_ = l_Lean_Compiler_Bytecode_Instruction_declConst(v_tgt_boxed_644_, v_id_boxed_645_);
v_r_647_ = lean_box_uint32(v_res_646_);
return v_r_647_;
}
}
LEAN_EXPORT uint32_t l_Lean_Compiler_Bytecode_Instruction_assemblerInternal(uint32_t v_idx_648_){
_start:
{
uint32_t v___x_649_; uint32_t v___x_650_; 
v___x_649_ = 4227858432;
v___x_650_ = lean_uint32_lor(v___x_649_, v_idx_648_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_assemblerInternal___boxed(lean_object* v_idx_651_){
_start:
{
uint32_t v_idx_boxed_652_; uint32_t v_res_653_; lean_object* v_r_654_; 
v_idx_boxed_652_ = lean_unbox_uint32(v_idx_651_);
lean_dec(v_idx_651_);
v_res_653_ = l_Lean_Compiler_Bytecode_Instruction_assemblerInternal(v_idx_boxed_652_);
v_r_654_ = lean_box_uint32(v_res_653_);
return v_r_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_pushInstr(lean_object* v_code_655_, uint32_t v_instr_656_){
_start:
{
uint8_t v___x_657_; lean_object* v_code_658_; uint32_t v___x_659_; uint32_t v___x_660_; uint8_t v___x_661_; lean_object* v_code_662_; uint32_t v___x_663_; uint32_t v___x_664_; uint8_t v___x_665_; lean_object* v_code_666_; uint32_t v___x_667_; uint32_t v___x_668_; uint8_t v___x_669_; lean_object* v___x_670_; 
v___x_657_ = lean_uint32_to_uint8(v_instr_656_);
v_code_658_ = lean_byte_array_push(v_code_655_, v___x_657_);
v___x_659_ = 8;
v___x_660_ = lean_uint32_shift_right(v_instr_656_, v___x_659_);
v___x_661_ = lean_uint32_to_uint8(v___x_660_);
v_code_662_ = lean_byte_array_push(v_code_658_, v___x_661_);
v___x_663_ = 16;
v___x_664_ = lean_uint32_shift_right(v_instr_656_, v___x_663_);
v___x_665_ = lean_uint32_to_uint8(v___x_664_);
v_code_666_ = lean_byte_array_push(v_code_662_, v___x_665_);
v___x_667_ = 24;
v___x_668_ = lean_uint32_shift_right(v_instr_656_, v___x_667_);
v___x_669_ = lean_uint32_to_uint8(v___x_668_);
v___x_670_ = lean_byte_array_push(v_code_666_, v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_pushInstr___boxed(lean_object* v_code_671_, lean_object* v_instr_672_){
_start:
{
uint32_t v_instr_boxed_673_; lean_object* v_res_674_; 
v_instr_boxed_673_ = lean_unbox_uint32(v_instr_672_);
lean_dec(v_instr_672_);
v_res_674_ = l_Lean_Compiler_Bytecode_pushInstr(v_code_671_, v_instr_boxed_673_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_assemble_spec__0(lean_object* v_as_675_, size_t v_i_676_, size_t v_stop_677_, lean_object* v_b_678_){
_start:
{
uint8_t v___x_679_; 
v___x_679_ = lean_usize_dec_eq(v_i_676_, v_stop_677_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; uint32_t v___x_681_; lean_object* v___x_682_; size_t v___x_683_; size_t v___x_684_; 
v___x_680_ = lean_array_uget_borrowed(v_as_675_, v_i_676_);
v___x_681_ = lean_unbox_uint32(v___x_680_);
v___x_682_ = l_Lean_Compiler_Bytecode_pushInstr(v_b_678_, v___x_681_);
v___x_683_ = ((size_t)1ULL);
v___x_684_ = lean_usize_add(v_i_676_, v___x_683_);
v_i_676_ = v___x_684_;
v_b_678_ = v___x_682_;
goto _start;
}
else
{
return v_b_678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_assemble_spec__0___boxed(lean_object* v_as_686_, lean_object* v_i_687_, lean_object* v_stop_688_, lean_object* v_b_689_){
_start:
{
size_t v_i_boxed_690_; size_t v_stop_boxed_691_; lean_object* v_res_692_; 
v_i_boxed_690_ = lean_unbox_usize(v_i_687_);
lean_dec(v_i_687_);
v_stop_boxed_691_ = lean_unbox_usize(v_stop_688_);
lean_dec(v_stop_688_);
v_res_692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_assemble_spec__0(v_as_686_, v_i_boxed_690_, v_stop_boxed_691_, v_b_689_);
lean_dec_ref(v_as_686_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_assemble(lean_object* v_instrs_693_){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_694_ = lean_array_get_size(v_instrs_693_);
v___x_695_ = lean_unsigned_to_nat(4u);
v___x_696_ = lean_nat_mul(v___x_694_, v___x_695_);
v___x_697_ = lean_mk_empty_byte_array(v___x_696_);
lean_dec(v___x_696_);
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = lean_nat_dec_lt(v___x_698_, v___x_694_);
if (v___x_699_ == 0)
{
return v___x_697_;
}
else
{
uint8_t v___x_700_; 
v___x_700_ = lean_nat_dec_le(v___x_694_, v___x_694_);
if (v___x_700_ == 0)
{
if (v___x_699_ == 0)
{
return v___x_697_;
}
else
{
size_t v___x_701_; size_t v___x_702_; lean_object* v___x_703_; 
v___x_701_ = ((size_t)0ULL);
v___x_702_ = lean_usize_of_nat(v___x_694_);
v___x_703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_assemble_spec__0(v_instrs_693_, v___x_701_, v___x_702_, v___x_697_);
return v___x_703_;
}
}
else
{
size_t v___x_704_; size_t v___x_705_; lean_object* v___x_706_; 
v___x_704_ = ((size_t)0ULL);
v___x_705_ = lean_usize_of_nat(v___x_694_);
v___x_706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_assemble_spec__0(v_instrs_693_, v___x_704_, v___x_705_, v___x_697_);
return v___x_706_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_assemble___boxed(lean_object* v_instrs_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_Compiler_Bytecode_assemble(v_instrs_707_);
lean_dec_ref(v_instrs_707_);
return v_res_708_;
}
}
static lean_object* _init_l_Lean_Compiler_Bytecode_addrToString___boxed__const__1(void){
_start:
{
uint32_t v___x_710_; lean_object* v___x_711_; 
v___x_710_ = 48;
v___x_711_ = lean_box_uint32(v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_addrToString(lean_object* v_addr_712_){
_start:
{
lean_object* v_addr_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v_addr_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v_addr_713_ = l_Int_toNat(v_addr_712_);
v___x_714_ = lean_unsigned_to_nat(4u);
v___x_715_ = lean_unsigned_to_nat(16u);
v___x_716_ = l_Nat_toDigits(v___x_715_, v_addr_713_);
v___x_717_ = l_List_lengthTR___redArg(v___x_716_);
v___x_718_ = lean_nat_sub(v___x_714_, v___x_717_);
lean_dec(v___x_717_);
v___x_719_ = l_Lean_Compiler_Bytecode_addrToString___boxed__const__1;
v_addr_720_ = l_List_replicateTR_loop___redArg(v___x_719_, v___x_718_, v___x_716_);
v___x_721_ = ((lean_object*)(l_Lean_Compiler_Bytecode_addrToString___closed__0));
v___x_722_ = lean_string_mk(v_addr_720_);
v___x_723_ = lean_string_append(v___x_721_, v___x_722_);
lean_dec_ref(v___x_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_addrToString___boxed(lean_object* v_addr_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_Compiler_Bytecode_addrToString(v_addr_724_);
lean_dec(v_addr_724_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Compiler_Bytecode_Instruction_toString_spec__0(lean_object* v_a_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = lean_nat_to_int(v_a_726_);
return v___x_727_;
}
}
static lean_object* _init_l_Lean_Compiler_Bytecode_Instruction_toString___closed__13(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_unsigned_to_nat(33554432u);
v___x_742_ = lean_nat_to_int(v___x_741_);
return v___x_742_;
}
}
static lean_object* _init_l_Lean_Compiler_Bytecode_Instruction_toString___closed__15(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_unsigned_to_nat(128u);
v___x_745_ = lean_nat_to_int(v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_toString(uint32_t v_instr_784_, lean_object* v_pos_785_){
_start:
{
uint32_t v___x_786_; uint32_t v___x_787_; uint32_t v_lo13_788_; uint32_t v___x_789_; uint32_t v___x_790_; uint32_t v___x_791_; uint32_t v_lo8_792_; uint32_t v___x_793_; uint32_t v_mid8_794_; uint32_t v___x_795_; uint32_t v___x_796_; uint32_t v___x_797_; uint32_t v___x_798_; uint32_t v_hi10_799_; uint32_t v_lo18_800_; uint32_t v___x_801_; uint32_t v___x_802_; uint32_t v_hi8_803_; uint32_t v___x_804_; uint32_t v___x_805_; uint32_t v_hi16_806_; uint32_t v_lo16_807_; uint32_t v___x_808_; uint32_t v___x_809_; uint32_t v_all_810_; uint32_t v___x_811_; uint32_t v___x_812_; uint8_t v___x_813_; 
v___x_786_ = 13;
v___x_787_ = 8191;
v_lo13_788_ = lean_uint32_land(v_instr_784_, v___x_787_);
v___x_789_ = lean_uint32_shift_right(v_instr_784_, v___x_786_);
v___x_790_ = 8;
v___x_791_ = 255;
v_lo8_792_ = lean_uint32_land(v_instr_784_, v___x_791_);
v___x_793_ = lean_uint32_shift_right(v_instr_784_, v___x_790_);
v_mid8_794_ = lean_uint32_land(v___x_793_, v___x_791_);
v___x_795_ = 16;
v___x_796_ = lean_uint32_shift_right(v_instr_784_, v___x_795_);
v___x_797_ = 10;
v___x_798_ = 1023;
v_hi10_799_ = lean_uint32_land(v___x_796_, v___x_798_);
v_lo18_800_ = lean_uint32_land(v_instr_784_, v___x_798_);
v___x_801_ = 18;
v___x_802_ = lean_uint32_shift_right(v_instr_784_, v___x_801_);
v_hi8_803_ = lean_uint32_land(v___x_802_, v___x_791_);
v___x_804_ = lean_uint32_shift_right(v_instr_784_, v___x_797_);
v___x_805_ = 65535;
v_hi16_806_ = lean_uint32_land(v___x_804_, v___x_805_);
v_lo16_807_ = lean_uint32_land(v_instr_784_, v___x_805_);
v___x_808_ = 26;
v___x_809_ = 67108863;
v_all_810_ = lean_uint32_land(v_instr_784_, v___x_809_);
v___x_811_ = lean_uint32_shift_right(v_instr_784_, v___x_808_);
v___x_812_ = 0;
v___x_813_ = lean_uint32_dec_eq(v___x_811_, v___x_812_);
if (v___x_813_ == 0)
{
uint32_t v___x_814_; uint32_t v_hi13_815_; uint8_t v___x_816_; 
v___x_814_ = 1;
v_hi13_815_ = lean_uint32_land(v___x_789_, v___x_787_);
v___x_816_ = lean_uint32_dec_eq(v___x_811_, v___x_814_);
if (v___x_816_ == 0)
{
uint32_t v___x_817_; uint8_t v___x_818_; 
v___x_817_ = 2;
v___x_818_ = lean_uint32_dec_eq(v___x_811_, v___x_817_);
if (v___x_818_ == 0)
{
uint32_t v___x_819_; uint8_t v___x_820_; 
v___x_819_ = 3;
v___x_820_ = lean_uint32_dec_eq(v___x_811_, v___x_819_);
if (v___x_820_ == 0)
{
uint32_t v___x_821_; uint8_t v___x_822_; 
v___x_821_ = 4;
v___x_822_ = lean_uint32_dec_eq(v___x_811_, v___x_821_);
if (v___x_822_ == 0)
{
uint32_t v___x_823_; uint8_t v___x_824_; 
v___x_823_ = 5;
v___x_824_ = lean_uint32_dec_eq(v___x_811_, v___x_823_);
if (v___x_824_ == 0)
{
uint32_t v_mid10_825_; uint32_t v___x_826_; uint8_t v___x_827_; 
v_mid10_825_ = lean_uint32_land(v___x_793_, v___x_798_);
v___x_826_ = 6;
v___x_827_ = lean_uint32_dec_eq(v___x_811_, v___x_826_);
if (v___x_827_ == 0)
{
uint32_t v___x_828_; uint8_t v___x_829_; 
v___x_828_ = 7;
v___x_829_ = lean_uint32_dec_eq(v___x_811_, v___x_828_);
if (v___x_829_ == 0)
{
uint8_t v___x_830_; 
v___x_830_ = lean_uint32_dec_eq(v___x_811_, v___x_790_);
if (v___x_830_ == 0)
{
uint32_t v___x_831_; uint32_t v_hi18_832_; uint32_t v___x_833_; uint8_t v___x_834_; 
v___x_831_ = 262143;
v_hi18_832_ = lean_uint32_land(v___x_793_, v___x_831_);
v___x_833_ = 9;
v___x_834_ = lean_uint32_dec_eq(v___x_811_, v___x_833_);
if (v___x_834_ == 0)
{
uint8_t v___x_835_; 
v___x_835_ = lean_uint32_dec_eq(v___x_811_, v___x_797_);
if (v___x_835_ == 0)
{
uint32_t v___x_836_; uint8_t v___x_837_; 
v___x_836_ = 11;
v___x_837_ = lean_uint32_dec_eq(v___x_811_, v___x_836_);
if (v___x_837_ == 0)
{
uint32_t v___x_838_; uint8_t v___x_839_; 
v___x_838_ = 12;
v___x_839_ = lean_uint32_dec_eq(v___x_811_, v___x_838_);
if (v___x_839_ == 0)
{
uint8_t v___x_840_; 
v___x_840_ = lean_uint32_dec_eq(v___x_811_, v___x_786_);
if (v___x_840_ == 0)
{
uint32_t v___x_841_; uint8_t v___x_842_; 
v___x_841_ = 14;
v___x_842_ = lean_uint32_dec_eq(v___x_811_, v___x_841_);
if (v___x_842_ == 0)
{
uint32_t v___x_843_; uint8_t v___x_844_; 
v___x_843_ = 15;
v___x_844_ = lean_uint32_dec_eq(v___x_811_, v___x_843_);
if (v___x_844_ == 0)
{
uint8_t v___x_845_; 
v___x_845_ = lean_uint32_dec_eq(v___x_811_, v___x_795_);
if (v___x_845_ == 0)
{
uint32_t v___x_846_; uint8_t v___x_847_; 
v___x_846_ = 17;
v___x_847_ = lean_uint32_dec_eq(v___x_811_, v___x_846_);
if (v___x_847_ == 0)
{
uint8_t v___x_848_; 
v___x_848_ = lean_uint32_dec_eq(v___x_811_, v___x_801_);
if (v___x_848_ == 0)
{
uint32_t v___x_849_; uint8_t v___x_850_; 
v___x_849_ = 19;
v___x_850_ = lean_uint32_dec_eq(v___x_811_, v___x_849_);
if (v___x_850_ == 0)
{
uint32_t v___x_851_; uint8_t v___x_852_; 
v___x_851_ = 20;
v___x_852_ = lean_uint32_dec_eq(v___x_811_, v___x_851_);
if (v___x_852_ == 0)
{
uint32_t v___x_853_; uint8_t v___x_854_; 
v___x_853_ = 21;
v___x_854_ = lean_uint32_dec_eq(v___x_811_, v___x_853_);
if (v___x_854_ == 0)
{
uint32_t v___x_855_; uint8_t v___x_856_; 
v___x_855_ = 22;
v___x_856_ = lean_uint32_dec_eq(v___x_811_, v___x_855_);
if (v___x_856_ == 0)
{
uint32_t v___x_857_; uint8_t v___x_858_; 
v___x_857_ = 23;
v___x_858_ = lean_uint32_dec_eq(v___x_811_, v___x_857_);
if (v___x_858_ == 0)
{
uint32_t v___x_859_; uint8_t v___x_860_; 
v___x_859_ = 24;
v___x_860_ = lean_uint32_dec_eq(v___x_811_, v___x_859_);
if (v___x_860_ == 0)
{
uint32_t v___x_861_; uint8_t v___x_862_; 
v___x_861_ = 25;
v___x_862_ = lean_uint32_dec_eq(v___x_811_, v___x_861_);
if (v___x_862_ == 0)
{
uint8_t v___x_863_; 
v___x_863_ = lean_uint32_dec_eq(v___x_811_, v___x_808_);
if (v___x_863_ == 0)
{
uint32_t v___x_864_; uint8_t v___x_865_; 
v___x_864_ = 27;
v___x_865_ = lean_uint32_dec_eq(v___x_811_, v___x_864_);
if (v___x_865_ == 0)
{
uint32_t v___x_866_; uint8_t v___x_867_; 
v___x_866_ = 28;
v___x_867_ = lean_uint32_dec_eq(v___x_811_, v___x_866_);
if (v___x_867_ == 0)
{
uint32_t v___x_868_; uint8_t v___x_869_; 
v___x_868_ = 29;
v___x_869_ = lean_uint32_dec_eq(v___x_811_, v___x_868_);
if (v___x_869_ == 0)
{
uint32_t v___x_870_; uint8_t v___x_871_; 
v___x_870_ = 30;
v___x_871_ = lean_uint32_dec_eq(v___x_811_, v___x_870_);
if (v___x_871_ == 0)
{
uint32_t v___x_872_; uint8_t v___x_873_; 
v___x_872_ = 31;
v___x_873_ = lean_uint32_dec_eq(v___x_811_, v___x_872_);
if (v___x_873_ == 0)
{
uint32_t v___x_874_; uint8_t v___x_875_; 
v___x_874_ = 32;
v___x_875_ = lean_uint32_dec_eq(v___x_811_, v___x_874_);
if (v___x_875_ == 0)
{
uint32_t v___x_876_; uint8_t v___x_877_; 
v___x_876_ = 33;
v___x_877_ = lean_uint32_dec_eq(v___x_811_, v___x_876_);
if (v___x_877_ == 0)
{
uint32_t v___x_878_; uint8_t v___x_879_; 
v___x_878_ = 34;
v___x_879_ = lean_uint32_dec_eq(v___x_811_, v___x_878_);
if (v___x_879_ == 0)
{
uint32_t v___x_880_; uint8_t v___x_881_; 
v___x_880_ = 35;
v___x_881_ = lean_uint32_dec_eq(v___x_811_, v___x_880_);
if (v___x_881_ == 0)
{
uint32_t v___x_882_; uint8_t v___x_883_; 
v___x_882_ = 36;
v___x_883_ = lean_uint32_dec_eq(v___x_811_, v___x_882_);
if (v___x_883_ == 0)
{
uint32_t v___x_884_; uint8_t v___x_885_; 
v___x_884_ = 37;
v___x_885_ = lean_uint32_dec_eq(v___x_811_, v___x_884_);
if (v___x_885_ == 0)
{
uint32_t v___x_886_; uint8_t v___x_887_; 
v___x_886_ = 38;
v___x_887_ = lean_uint32_dec_eq(v___x_811_, v___x_886_);
if (v___x_887_ == 0)
{
uint32_t v___x_888_; uint8_t v___x_889_; 
v___x_888_ = 39;
v___x_889_ = lean_uint32_dec_eq(v___x_811_, v___x_888_);
if (v___x_889_ == 0)
{
uint32_t v___x_890_; uint8_t v___x_891_; 
v___x_890_ = 40;
v___x_891_ = lean_uint32_dec_eq(v___x_811_, v___x_890_);
if (v___x_891_ == 0)
{
uint32_t v___x_892_; uint8_t v___x_893_; 
v___x_892_ = 41;
v___x_893_ = lean_uint32_dec_eq(v___x_811_, v___x_892_);
if (v___x_893_ == 0)
{
uint32_t v___x_894_; uint8_t v___x_895_; 
v___x_894_ = 42;
v___x_895_ = lean_uint32_dec_eq(v___x_811_, v___x_894_);
if (v___x_895_ == 0)
{
uint32_t v___x_896_; uint8_t v___x_897_; 
v___x_896_ = 43;
v___x_897_ = lean_uint32_dec_eq(v___x_811_, v___x_896_);
if (v___x_897_ == 0)
{
uint32_t v___x_898_; uint8_t v___x_899_; 
v___x_898_ = 44;
v___x_899_ = lean_uint32_dec_eq(v___x_811_, v___x_898_);
if (v___x_899_ == 0)
{
uint32_t v___x_900_; uint8_t v___x_901_; 
v___x_900_ = 45;
v___x_901_ = lean_uint32_dec_eq(v___x_811_, v___x_900_);
if (v___x_901_ == 0)
{
uint32_t v___x_902_; uint8_t v___x_903_; 
v___x_902_ = 46;
v___x_903_ = lean_uint32_dec_eq(v___x_811_, v___x_902_);
if (v___x_903_ == 0)
{
uint32_t v___x_904_; uint8_t v___x_905_; 
lean_dec(v_pos_785_);
v___x_904_ = 47;
v___x_905_ = lean_uint32_dec_eq(v___x_811_, v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_906_ = ((lean_object*)(l_Lean_Compiler_Bytecode_addrToString___closed__0));
v___x_907_ = lean_unsigned_to_nat(32u);
v___x_908_ = lean_uint32_to_nat(v_instr_784_);
v___x_909_ = l_BitVec_toHex(v___x_907_, v___x_908_);
v___x_910_ = lean_string_append(v___x_906_, v___x_909_);
lean_dec_ref(v___x_909_);
return v___x_910_;
}
else
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_911_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__0));
v___x_912_ = lean_uint32_to_nat(v_hi18_832_);
v___x_913_ = l_Nat_reprFast(v___x_912_);
v___x_914_ = lean_string_append(v___x_911_, v___x_913_);
lean_dec_ref(v___x_913_);
v___x_915_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__1));
v___x_916_ = lean_string_append(v___x_914_, v___x_915_);
v___x_917_ = lean_uint32_to_nat(v_lo8_792_);
v___x_918_ = l_Nat_reprFast(v___x_917_);
v___x_919_ = lean_string_append(v___x_916_, v___x_918_);
lean_dec_ref(v___x_918_);
return v___x_919_;
}
}
else
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_920_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__2));
v___x_921_ = lean_nat_to_int(v_pos_785_);
v___x_922_ = lean_uint32_to_nat(v_all_810_);
v___x_923_ = lean_nat_to_int(v___x_922_);
v___x_924_ = lean_int_add(v___x_921_, v___x_923_);
lean_dec(v___x_923_);
lean_dec(v___x_921_);
v___x_925_ = l_Lean_Compiler_Bytecode_addrToString(v___x_924_);
lean_dec(v___x_924_);
v___x_926_ = lean_string_append(v___x_920_, v___x_925_);
lean_dec_ref(v___x_925_);
return v___x_926_;
}
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
lean_dec(v_pos_785_);
v___x_927_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__3));
v___x_928_ = lean_uint32_to_nat(v_lo8_792_);
v___x_929_ = l_Nat_reprFast(v___x_928_);
v___x_930_ = lean_string_append(v___x_927_, v___x_929_);
lean_dec_ref(v___x_929_);
return v___x_930_;
}
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
lean_dec(v_pos_785_);
v___x_931_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__4));
v___x_932_ = lean_uint32_to_nat(v_hi8_803_);
v___x_933_ = l_Nat_reprFast(v___x_932_);
v___x_934_ = lean_string_append(v___x_931_, v___x_933_);
lean_dec_ref(v___x_933_);
v___x_935_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_936_ = lean_string_append(v___x_934_, v___x_935_);
v___x_937_ = lean_uint32_to_nat(v_mid10_825_);
v___x_938_ = l_Nat_reprFast(v___x_937_);
v___x_939_ = lean_string_append(v___x_936_, v___x_938_);
lean_dec_ref(v___x_938_);
v___x_940_ = lean_string_append(v___x_939_, v___x_935_);
v___x_941_ = lean_uint32_to_nat(v_lo8_792_);
v___x_942_ = l_Nat_reprFast(v___x_941_);
v___x_943_ = lean_string_append(v___x_940_, v___x_942_);
lean_dec_ref(v___x_942_);
return v___x_943_;
}
}
else
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
lean_dec(v_pos_785_);
v___x_944_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__6));
v___x_945_ = lean_uint32_to_nat(v_hi10_799_);
v___x_946_ = l_Nat_reprFast(v___x_945_);
v___x_947_ = lean_string_append(v___x_944_, v___x_946_);
lean_dec_ref(v___x_946_);
v___x_948_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_949_ = lean_string_append(v___x_947_, v___x_948_);
v___x_950_ = lean_uint32_to_nat(v_mid8_794_);
v___x_951_ = l_Nat_reprFast(v___x_950_);
v___x_952_ = lean_string_append(v___x_949_, v___x_951_);
lean_dec_ref(v___x_951_);
v___x_953_ = lean_string_append(v___x_952_, v___x_948_);
v___x_954_ = lean_uint32_to_nat(v_lo8_792_);
v___x_955_ = l_Nat_reprFast(v___x_954_);
v___x_956_ = lean_string_append(v___x_953_, v___x_955_);
lean_dec_ref(v___x_955_);
return v___x_956_;
}
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
lean_dec(v_pos_785_);
v___x_957_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__8));
v___x_958_ = lean_uint32_to_nat(v_lo8_792_);
v___x_959_ = l_Nat_reprFast(v___x_958_);
v___x_960_ = lean_string_append(v___x_957_, v___x_959_);
lean_dec_ref(v___x_959_);
return v___x_960_;
}
}
else
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
lean_dec(v_pos_785_);
v___x_961_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__9));
v___x_962_ = lean_uint32_to_nat(v_hi10_799_);
v___x_963_ = l_Nat_reprFast(v___x_962_);
v___x_964_ = lean_string_append(v___x_961_, v___x_963_);
lean_dec_ref(v___x_963_);
v___x_965_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__10));
v___x_966_ = lean_string_append(v___x_964_, v___x_965_);
v___x_967_ = lean_uint32_to_nat(v_lo16_807_);
v___x_968_ = l_Nat_reprFast(v___x_967_);
v___x_969_ = lean_string_append(v___x_966_, v___x_968_);
lean_dec_ref(v___x_968_);
return v___x_969_;
}
}
else
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
lean_dec(v_pos_785_);
v___x_970_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__11));
v___x_971_ = lean_uint32_to_nat(v_hi10_799_);
v___x_972_ = l_Nat_reprFast(v___x_971_);
v___x_973_ = lean_string_append(v___x_970_, v___x_972_);
lean_dec_ref(v___x_972_);
v___x_974_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_975_ = lean_string_append(v___x_973_, v___x_974_);
v___x_976_ = lean_uint32_to_nat(v_lo16_807_);
v___x_977_ = l_Nat_reprFast(v___x_976_);
v___x_978_ = lean_string_append(v___x_975_, v___x_977_);
lean_dec_ref(v___x_977_);
return v___x_978_;
}
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_979_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__12));
v___x_980_ = lean_nat_to_int(v_pos_785_);
v___x_981_ = lean_uint32_to_nat(v_all_810_);
v___x_982_ = lean_nat_to_int(v___x_981_);
v___x_983_ = lean_int_add(v___x_980_, v___x_982_);
lean_dec(v___x_982_);
lean_dec(v___x_980_);
v___x_984_ = lean_obj_once(&l_Lean_Compiler_Bytecode_Instruction_toString___closed__13, &l_Lean_Compiler_Bytecode_Instruction_toString___closed__13_once, _init_l_Lean_Compiler_Bytecode_Instruction_toString___closed__13);
v___x_985_ = lean_int_sub(v___x_983_, v___x_984_);
lean_dec(v___x_983_);
v___x_986_ = l_Lean_Compiler_Bytecode_addrToString(v___x_985_);
lean_dec(v___x_985_);
v___x_987_ = lean_string_append(v___x_979_, v___x_986_);
lean_dec_ref(v___x_986_);
return v___x_987_;
}
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_988_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__14));
v___x_989_ = lean_uint32_to_nat(v_hi8_803_);
v___x_990_ = l_Nat_reprFast(v___x_989_);
v___x_991_ = lean_string_append(v___x_988_, v___x_990_);
lean_dec_ref(v___x_990_);
v___x_992_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_993_ = lean_string_append(v___x_991_, v___x_992_);
v___x_994_ = lean_uint32_to_nat(v_mid10_825_);
v___x_995_ = l_Nat_reprFast(v___x_994_);
v___x_996_ = lean_string_append(v___x_993_, v___x_995_);
lean_dec_ref(v___x_995_);
v___x_997_ = lean_string_append(v___x_996_, v___x_992_);
v___x_998_ = lean_nat_to_int(v_pos_785_);
v___x_999_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1000_ = lean_nat_to_int(v___x_999_);
v___x_1001_ = lean_int_add(v___x_998_, v___x_1000_);
lean_dec(v___x_1000_);
lean_dec(v___x_998_);
v___x_1002_ = lean_obj_once(&l_Lean_Compiler_Bytecode_Instruction_toString___closed__15, &l_Lean_Compiler_Bytecode_Instruction_toString___closed__15_once, _init_l_Lean_Compiler_Bytecode_Instruction_toString___closed__15);
v___x_1003_ = lean_int_sub(v___x_1001_, v___x_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = l_Lean_Compiler_Bytecode_addrToString(v___x_1003_);
lean_dec(v___x_1003_);
v___x_1005_ = lean_string_append(v___x_997_, v___x_1004_);
lean_dec_ref(v___x_1004_);
return v___x_1005_;
}
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_dec(v_pos_785_);
v___x_1006_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__16));
v___x_1007_ = lean_uint32_to_nat(v_all_810_);
v___x_1008_ = l_Nat_reprFast(v___x_1007_);
v___x_1009_ = lean_string_append(v___x_1006_, v___x_1008_);
lean_dec_ref(v___x_1008_);
return v___x_1009_;
}
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
lean_dec(v_pos_785_);
v___x_1010_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__17));
v___x_1011_ = lean_uint32_to_nat(v_hi16_806_);
v___x_1012_ = l_Nat_reprFast(v___x_1011_);
v___x_1013_ = lean_string_append(v___x_1010_, v___x_1012_);
lean_dec_ref(v___x_1012_);
v___x_1014_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_1015_ = lean_string_append(v___x_1013_, v___x_1014_);
v___x_1016_ = lean_uint32_to_nat(v_lo18_800_);
v___x_1017_ = l_Nat_reprFast(v___x_1016_);
v___x_1018_ = lean_string_append(v___x_1015_, v___x_1017_);
lean_dec_ref(v___x_1017_);
return v___x_1018_;
}
}
else
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
lean_dec(v_pos_785_);
v___x_1019_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__18));
v___x_1020_ = lean_uint32_to_nat(v_hi16_806_);
v___x_1021_ = l_Nat_reprFast(v___x_1020_);
v___x_1022_ = lean_string_append(v___x_1019_, v___x_1021_);
lean_dec_ref(v___x_1021_);
v___x_1023_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_1024_ = lean_string_append(v___x_1022_, v___x_1023_);
v___x_1025_ = lean_uint32_to_nat(v_lo18_800_);
v___x_1026_ = l_Nat_reprFast(v___x_1025_);
v___x_1027_ = lean_string_append(v___x_1024_, v___x_1026_);
lean_dec_ref(v___x_1026_);
return v___x_1027_;
}
}
else
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
lean_dec(v_pos_785_);
v___x_1028_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__19));
v___x_1029_ = lean_uint32_to_nat(v_hi18_832_);
v___x_1030_ = l_Nat_reprFast(v___x_1029_);
v___x_1031_ = lean_string_append(v___x_1028_, v___x_1030_);
lean_dec_ref(v___x_1030_);
v___x_1032_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1033_ = lean_string_append(v___x_1031_, v___x_1032_);
v___x_1034_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1035_ = l_Nat_reprFast(v___x_1034_);
v___x_1036_ = lean_string_append(v___x_1033_, v___x_1035_);
lean_dec_ref(v___x_1035_);
return v___x_1036_;
}
}
else
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_dec(v_pos_785_);
v___x_1037_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__20));
v___x_1038_ = lean_uint32_to_nat(v_hi18_832_);
v___x_1039_ = l_Nat_reprFast(v___x_1038_);
v___x_1040_ = lean_string_append(v___x_1037_, v___x_1039_);
lean_dec_ref(v___x_1039_);
v___x_1041_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1042_ = lean_string_append(v___x_1040_, v___x_1041_);
v___x_1043_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1044_ = l_Nat_reprFast(v___x_1043_);
v___x_1045_ = lean_string_append(v___x_1042_, v___x_1044_);
lean_dec_ref(v___x_1044_);
return v___x_1045_;
}
}
else
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_dec(v_pos_785_);
v___x_1046_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__21));
v___x_1047_ = lean_uint32_to_nat(v_hi18_832_);
v___x_1048_ = l_Nat_reprFast(v___x_1047_);
v___x_1049_ = lean_string_append(v___x_1046_, v___x_1048_);
lean_dec_ref(v___x_1048_);
v___x_1050_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_1051_ = lean_string_append(v___x_1049_, v___x_1050_);
v___x_1052_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1053_ = l_Nat_reprFast(v___x_1052_);
v___x_1054_ = lean_string_append(v___x_1051_, v___x_1053_);
lean_dec_ref(v___x_1053_);
return v___x_1054_;
}
}
else
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
lean_dec(v_pos_785_);
v___x_1055_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__22));
v___x_1056_ = lean_uint32_to_nat(v_hi18_832_);
v___x_1057_ = l_Nat_reprFast(v___x_1056_);
v___x_1058_ = lean_string_append(v___x_1055_, v___x_1057_);
lean_dec_ref(v___x_1057_);
v___x_1059_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_1060_ = lean_string_append(v___x_1058_, v___x_1059_);
v___x_1061_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1062_ = l_Nat_reprFast(v___x_1061_);
v___x_1063_ = lean_string_append(v___x_1060_, v___x_1062_);
lean_dec_ref(v___x_1062_);
return v___x_1063_;
}
}
else
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
lean_dec(v_pos_785_);
v___x_1064_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__23));
v___x_1065_ = lean_uint32_to_nat(v_hi18_832_);
v___x_1066_ = l_Nat_reprFast(v___x_1065_);
v___x_1067_ = lean_string_append(v___x_1064_, v___x_1066_);
lean_dec_ref(v___x_1066_);
v___x_1068_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1069_ = lean_string_append(v___x_1067_, v___x_1068_);
v___x_1070_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1071_ = l_Nat_reprFast(v___x_1070_);
v___x_1072_ = lean_string_append(v___x_1069_, v___x_1071_);
lean_dec_ref(v___x_1071_);
return v___x_1072_;
}
}
else
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_dec(v_pos_785_);
v___x_1073_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__24));
v___x_1074_ = lean_uint32_to_nat(v_hi18_832_);
v___x_1075_ = l_Nat_reprFast(v___x_1074_);
v___x_1076_ = lean_string_append(v___x_1073_, v___x_1075_);
lean_dec_ref(v___x_1075_);
v___x_1077_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1078_ = lean_string_append(v___x_1076_, v___x_1077_);
v___x_1079_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1080_ = l_Nat_reprFast(v___x_1079_);
v___x_1081_ = lean_string_append(v___x_1078_, v___x_1080_);
lean_dec_ref(v___x_1080_);
return v___x_1081_;
}
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
lean_dec(v_pos_785_);
v___x_1082_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__25));
v___x_1083_ = lean_uint32_to_nat(v_hi18_832_);
v___x_1084_ = l_Nat_reprFast(v___x_1083_);
v___x_1085_ = lean_string_append(v___x_1082_, v___x_1084_);
lean_dec_ref(v___x_1084_);
v___x_1086_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1087_ = lean_string_append(v___x_1085_, v___x_1086_);
v___x_1088_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1089_ = l_Nat_reprFast(v___x_1088_);
v___x_1090_ = lean_string_append(v___x_1087_, v___x_1089_);
lean_dec_ref(v___x_1089_);
return v___x_1090_;
}
}
else
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_dec(v_pos_785_);
v___x_1091_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__26));
v___x_1092_ = lean_uint32_to_nat(v_hi18_832_);
v___x_1093_ = l_Nat_reprFast(v___x_1092_);
v___x_1094_ = lean_string_append(v___x_1091_, v___x_1093_);
lean_dec_ref(v___x_1093_);
v___x_1095_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1096_ = lean_string_append(v___x_1094_, v___x_1095_);
v___x_1097_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1098_ = l_Nat_reprFast(v___x_1097_);
v___x_1099_ = lean_string_append(v___x_1096_, v___x_1098_);
lean_dec_ref(v___x_1098_);
return v___x_1099_;
}
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_dec(v_pos_785_);
v___x_1100_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__27));
v___x_1101_ = lean_uint32_to_nat(v_hi18_832_);
v___x_1102_ = l_Nat_reprFast(v___x_1101_);
v___x_1103_ = lean_string_append(v___x_1100_, v___x_1102_);
lean_dec_ref(v___x_1102_);
v___x_1104_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1105_ = lean_string_append(v___x_1103_, v___x_1104_);
v___x_1106_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1107_ = l_Nat_reprFast(v___x_1106_);
v___x_1108_ = lean_string_append(v___x_1105_, v___x_1107_);
lean_dec_ref(v___x_1107_);
return v___x_1108_;
}
}
else
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_dec(v_pos_785_);
v___x_1109_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__28));
v___x_1110_ = lean_uint32_to_nat(v_hi18_832_);
v___x_1111_ = l_Nat_reprFast(v___x_1110_);
v___x_1112_ = lean_string_append(v___x_1109_, v___x_1111_);
lean_dec_ref(v___x_1111_);
v___x_1113_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1114_ = lean_string_append(v___x_1112_, v___x_1113_);
v___x_1115_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1116_ = l_Nat_reprFast(v___x_1115_);
v___x_1117_ = lean_string_append(v___x_1114_, v___x_1116_);
lean_dec_ref(v___x_1116_);
return v___x_1117_;
}
}
else
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
lean_dec(v_pos_785_);
v___x_1118_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__29));
v___x_1119_ = lean_uint32_to_nat(v_hi18_832_);
v___x_1120_ = l_Nat_reprFast(v___x_1119_);
v___x_1121_ = lean_string_append(v___x_1118_, v___x_1120_);
lean_dec_ref(v___x_1120_);
v___x_1122_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1123_ = lean_string_append(v___x_1121_, v___x_1122_);
v___x_1124_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1125_ = l_Nat_reprFast(v___x_1124_);
v___x_1126_ = lean_string_append(v___x_1123_, v___x_1125_);
lean_dec_ref(v___x_1125_);
return v___x_1126_;
}
}
else
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_dec(v_pos_785_);
v___x_1127_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__30));
v___x_1128_ = lean_uint32_to_nat(v_hi18_832_);
v___x_1129_ = l_Nat_reprFast(v___x_1128_);
v___x_1130_ = lean_string_append(v___x_1127_, v___x_1129_);
lean_dec_ref(v___x_1129_);
v___x_1131_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1132_ = lean_string_append(v___x_1130_, v___x_1131_);
v___x_1133_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1134_ = l_Nat_reprFast(v___x_1133_);
v___x_1135_ = lean_string_append(v___x_1132_, v___x_1134_);
lean_dec_ref(v___x_1134_);
return v___x_1135_;
}
}
else
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_dec(v_pos_785_);
v___x_1136_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__31));
v___x_1137_ = lean_uint32_to_nat(v_hi18_832_);
v___x_1138_ = l_Nat_reprFast(v___x_1137_);
v___x_1139_ = lean_string_append(v___x_1136_, v___x_1138_);
lean_dec_ref(v___x_1138_);
v___x_1140_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1141_ = lean_string_append(v___x_1139_, v___x_1140_);
v___x_1142_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1143_ = l_Nat_reprFast(v___x_1142_);
v___x_1144_ = lean_string_append(v___x_1141_, v___x_1143_);
lean_dec_ref(v___x_1143_);
return v___x_1144_;
}
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_dec(v_pos_785_);
v___x_1145_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__32));
v___x_1146_ = lean_uint32_to_nat(v_hi18_832_);
v___x_1147_ = l_Nat_reprFast(v___x_1146_);
v___x_1148_ = lean_string_append(v___x_1145_, v___x_1147_);
lean_dec_ref(v___x_1147_);
v___x_1149_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1150_ = lean_string_append(v___x_1148_, v___x_1149_);
v___x_1151_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1152_ = l_Nat_reprFast(v___x_1151_);
v___x_1153_ = lean_string_append(v___x_1150_, v___x_1152_);
lean_dec_ref(v___x_1152_);
return v___x_1153_;
}
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_dec(v_pos_785_);
v___x_1154_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__33));
v___x_1155_ = lean_uint32_to_nat(v_hi18_832_);
v___x_1156_ = l_Nat_reprFast(v___x_1155_);
v___x_1157_ = lean_string_append(v___x_1154_, v___x_1156_);
lean_dec_ref(v___x_1156_);
v___x_1158_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1159_ = lean_string_append(v___x_1157_, v___x_1158_);
v___x_1160_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1161_ = l_Nat_reprFast(v___x_1160_);
v___x_1162_ = lean_string_append(v___x_1159_, v___x_1161_);
lean_dec_ref(v___x_1161_);
return v___x_1162_;
}
}
else
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
lean_dec(v_pos_785_);
v___x_1163_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__34));
v___x_1164_ = lean_uint32_to_nat(v_hi18_832_);
v___x_1165_ = l_Nat_reprFast(v___x_1164_);
v___x_1166_ = lean_string_append(v___x_1163_, v___x_1165_);
lean_dec_ref(v___x_1165_);
v___x_1167_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1168_ = lean_string_append(v___x_1166_, v___x_1167_);
v___x_1169_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1170_ = l_Nat_reprFast(v___x_1169_);
v___x_1171_ = lean_string_append(v___x_1168_, v___x_1170_);
lean_dec_ref(v___x_1170_);
return v___x_1171_;
}
}
else
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_dec(v_pos_785_);
v___x_1172_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__35));
v___x_1173_ = lean_uint32_to_nat(v_hi18_832_);
v___x_1174_ = l_Nat_reprFast(v___x_1173_);
v___x_1175_ = lean_string_append(v___x_1172_, v___x_1174_);
lean_dec_ref(v___x_1174_);
v___x_1176_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1177_ = lean_string_append(v___x_1175_, v___x_1176_);
v___x_1178_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1179_ = l_Nat_reprFast(v___x_1178_);
v___x_1180_ = lean_string_append(v___x_1177_, v___x_1179_);
lean_dec_ref(v___x_1179_);
return v___x_1180_;
}
}
else
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_dec(v_pos_785_);
v___x_1181_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__36));
v___x_1182_ = lean_uint32_to_nat(v_hi18_832_);
v___x_1183_ = l_Nat_reprFast(v___x_1182_);
v___x_1184_ = lean_string_append(v___x_1181_, v___x_1183_);
lean_dec_ref(v___x_1183_);
v___x_1185_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1186_ = lean_string_append(v___x_1184_, v___x_1185_);
v___x_1187_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1188_ = l_Nat_reprFast(v___x_1187_);
v___x_1189_ = lean_string_append(v___x_1186_, v___x_1188_);
lean_dec_ref(v___x_1188_);
return v___x_1189_;
}
}
else
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
lean_dec(v_pos_785_);
v___x_1190_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__37));
v___x_1191_ = lean_uint32_to_nat(v_hi18_832_);
v___x_1192_ = l_Nat_reprFast(v___x_1191_);
v___x_1193_ = lean_string_append(v___x_1190_, v___x_1192_);
lean_dec_ref(v___x_1192_);
v___x_1194_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1195_ = lean_string_append(v___x_1193_, v___x_1194_);
v___x_1196_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1197_ = l_Nat_reprFast(v___x_1196_);
v___x_1198_ = lean_string_append(v___x_1195_, v___x_1197_);
lean_dec_ref(v___x_1197_);
return v___x_1198_;
}
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
lean_dec(v_pos_785_);
v___x_1199_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__38));
v___x_1200_ = lean_uint32_to_nat(v_hi18_832_);
v___x_1201_ = l_Nat_reprFast(v___x_1200_);
v___x_1202_ = lean_string_append(v___x_1199_, v___x_1201_);
lean_dec_ref(v___x_1201_);
v___x_1203_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1204_ = lean_string_append(v___x_1202_, v___x_1203_);
v___x_1205_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1206_ = l_Nat_reprFast(v___x_1205_);
v___x_1207_ = lean_string_append(v___x_1204_, v___x_1206_);
lean_dec_ref(v___x_1206_);
return v___x_1207_;
}
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_dec(v_pos_785_);
v___x_1208_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__39));
v___x_1209_ = lean_uint32_to_nat(v_hi10_799_);
v___x_1210_ = l_Nat_reprFast(v___x_1209_);
v___x_1211_ = lean_string_append(v___x_1208_, v___x_1210_);
lean_dec_ref(v___x_1210_);
v___x_1212_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1213_ = lean_string_append(v___x_1211_, v___x_1212_);
v___x_1214_ = lean_uint32_to_nat(v_mid8_794_);
v___x_1215_ = l_Nat_reprFast(v___x_1214_);
v___x_1216_ = lean_string_append(v___x_1213_, v___x_1215_);
lean_dec_ref(v___x_1215_);
v___x_1217_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_1218_ = lean_string_append(v___x_1216_, v___x_1217_);
v___x_1219_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1220_ = l_Nat_reprFast(v___x_1219_);
v___x_1221_ = lean_string_append(v___x_1218_, v___x_1220_);
lean_dec_ref(v___x_1220_);
return v___x_1221_;
}
}
else
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
lean_dec(v_pos_785_);
v___x_1222_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__40));
v___x_1223_ = lean_uint32_to_nat(v_hi10_799_);
v___x_1224_ = l_Nat_reprFast(v___x_1223_);
v___x_1225_ = lean_string_append(v___x_1222_, v___x_1224_);
lean_dec_ref(v___x_1224_);
v___x_1226_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1227_ = lean_string_append(v___x_1225_, v___x_1226_);
v___x_1228_ = lean_uint32_to_nat(v_mid8_794_);
v___x_1229_ = l_Nat_reprFast(v___x_1228_);
v___x_1230_ = lean_string_append(v___x_1227_, v___x_1229_);
lean_dec_ref(v___x_1229_);
v___x_1231_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_1232_ = lean_string_append(v___x_1230_, v___x_1231_);
v___x_1233_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1234_ = l_Nat_reprFast(v___x_1233_);
v___x_1235_ = lean_string_append(v___x_1232_, v___x_1234_);
lean_dec_ref(v___x_1234_);
return v___x_1235_;
}
}
else
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_dec(v_pos_785_);
v___x_1236_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__41));
v___x_1237_ = lean_uint32_to_nat(v_hi18_832_);
v___x_1238_ = l_Nat_reprFast(v___x_1237_);
v___x_1239_ = lean_string_append(v___x_1236_, v___x_1238_);
lean_dec_ref(v___x_1238_);
v___x_1240_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1241_ = lean_string_append(v___x_1239_, v___x_1240_);
v___x_1242_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1243_ = l_Nat_reprFast(v___x_1242_);
v___x_1244_ = lean_string_append(v___x_1241_, v___x_1243_);
lean_dec_ref(v___x_1243_);
return v___x_1244_;
}
}
else
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_dec(v_pos_785_);
v___x_1245_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__42));
v___x_1246_ = lean_uint32_to_nat(v_hi18_832_);
v___x_1247_ = l_Nat_reprFast(v___x_1246_);
v___x_1248_ = lean_string_append(v___x_1245_, v___x_1247_);
lean_dec_ref(v___x_1247_);
v___x_1249_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1250_ = lean_string_append(v___x_1248_, v___x_1249_);
v___x_1251_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1252_ = l_Nat_reprFast(v___x_1251_);
v___x_1253_ = lean_string_append(v___x_1250_, v___x_1252_);
lean_dec_ref(v___x_1252_);
return v___x_1253_;
}
}
else
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
lean_dec(v_pos_785_);
v___x_1254_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__43));
v___x_1255_ = lean_uint32_to_nat(v_hi18_832_);
v___x_1256_ = l_Nat_reprFast(v___x_1255_);
v___x_1257_ = lean_string_append(v___x_1254_, v___x_1256_);
lean_dec_ref(v___x_1256_);
v___x_1258_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1259_ = lean_string_append(v___x_1257_, v___x_1258_);
v___x_1260_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1261_ = l_Nat_reprFast(v___x_1260_);
v___x_1262_ = lean_string_append(v___x_1259_, v___x_1261_);
lean_dec_ref(v___x_1261_);
return v___x_1262_;
}
}
else
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec(v_pos_785_);
v___x_1263_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__44));
v___x_1264_ = lean_uint32_to_nat(v_hi18_832_);
v___x_1265_ = l_Nat_reprFast(v___x_1264_);
v___x_1266_ = lean_string_append(v___x_1263_, v___x_1265_);
lean_dec_ref(v___x_1265_);
v___x_1267_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1268_ = lean_string_append(v___x_1266_, v___x_1267_);
v___x_1269_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1270_ = l_Nat_reprFast(v___x_1269_);
v___x_1271_ = lean_string_append(v___x_1268_, v___x_1270_);
lean_dec_ref(v___x_1270_);
return v___x_1271_;
}
}
else
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
lean_dec(v_pos_785_);
v___x_1272_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__45));
v___x_1273_ = lean_uint32_to_nat(v_hi10_799_);
v___x_1274_ = l_Nat_reprFast(v___x_1273_);
v___x_1275_ = lean_string_append(v___x_1272_, v___x_1274_);
lean_dec_ref(v___x_1274_);
v___x_1276_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1277_ = lean_string_append(v___x_1275_, v___x_1276_);
v___x_1278_ = lean_uint32_to_nat(v_mid8_794_);
v___x_1279_ = l_Nat_reprFast(v___x_1278_);
v___x_1280_ = lean_string_append(v___x_1277_, v___x_1279_);
lean_dec_ref(v___x_1279_);
v___x_1281_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_1282_ = lean_string_append(v___x_1280_, v___x_1281_);
v___x_1283_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1284_ = l_Nat_reprFast(v___x_1283_);
v___x_1285_ = lean_string_append(v___x_1282_, v___x_1284_);
lean_dec_ref(v___x_1284_);
return v___x_1285_;
}
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
lean_dec(v_pos_785_);
v___x_1286_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__46));
v___x_1287_ = lean_uint32_to_nat(v_hi10_799_);
v___x_1288_ = l_Nat_reprFast(v___x_1287_);
v___x_1289_ = lean_string_append(v___x_1286_, v___x_1288_);
lean_dec_ref(v___x_1288_);
v___x_1290_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1291_ = lean_string_append(v___x_1289_, v___x_1290_);
v___x_1292_ = lean_uint32_to_nat(v_mid8_794_);
v___x_1293_ = l_Nat_reprFast(v___x_1292_);
v___x_1294_ = lean_string_append(v___x_1291_, v___x_1293_);
lean_dec_ref(v___x_1293_);
v___x_1295_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_1296_ = lean_string_append(v___x_1294_, v___x_1295_);
v___x_1297_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1298_ = l_Nat_reprFast(v___x_1297_);
v___x_1299_ = lean_string_append(v___x_1296_, v___x_1298_);
lean_dec_ref(v___x_1298_);
return v___x_1299_;
}
}
else
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
lean_dec(v_pos_785_);
v___x_1300_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__47));
v___x_1301_ = lean_uint32_to_nat(v_hi8_803_);
v___x_1302_ = l_Nat_reprFast(v___x_1301_);
v___x_1303_ = lean_string_append(v___x_1300_, v___x_1302_);
lean_dec_ref(v___x_1302_);
v___x_1304_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_1305_ = lean_string_append(v___x_1303_, v___x_1304_);
v___x_1306_ = lean_uint32_to_nat(v_mid10_825_);
v___x_1307_ = l_Nat_reprFast(v___x_1306_);
v___x_1308_ = lean_string_append(v___x_1305_, v___x_1307_);
lean_dec_ref(v___x_1307_);
v___x_1309_ = lean_string_append(v___x_1308_, v___x_1304_);
v___x_1310_ = lean_uint32_to_nat(v_lo8_792_);
v___x_1311_ = l_Nat_reprFast(v___x_1310_);
v___x_1312_ = lean_string_append(v___x_1309_, v___x_1311_);
lean_dec_ref(v___x_1311_);
return v___x_1312_;
}
}
else
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
lean_dec(v_pos_785_);
v___x_1313_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__48));
v___x_1314_ = lean_uint32_to_nat(v_hi13_815_);
v___x_1315_ = l_Nat_reprFast(v___x_1314_);
v___x_1316_ = lean_string_append(v___x_1313_, v___x_1315_);
lean_dec_ref(v___x_1315_);
v___x_1317_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_1318_ = lean_string_append(v___x_1316_, v___x_1317_);
v___x_1319_ = lean_uint32_to_nat(v_lo13_788_);
v___x_1320_ = l_Nat_reprFast(v___x_1319_);
v___x_1321_ = lean_string_append(v___x_1318_, v___x_1320_);
lean_dec_ref(v___x_1320_);
return v___x_1321_;
}
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
lean_dec(v_pos_785_);
v___x_1322_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__49));
v___x_1323_ = lean_uint32_to_nat(v_all_810_);
v___x_1324_ = l_Nat_reprFast(v___x_1323_);
v___x_1325_ = lean_string_append(v___x_1322_, v___x_1324_);
lean_dec_ref(v___x_1324_);
return v___x_1325_;
}
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
lean_dec(v_pos_785_);
v___x_1326_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__50));
v___x_1327_ = lean_uint32_to_nat(v_all_810_);
v___x_1328_ = l_Nat_reprFast(v___x_1327_);
v___x_1329_ = lean_string_append(v___x_1326_, v___x_1328_);
lean_dec_ref(v___x_1328_);
return v___x_1329_;
}
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
lean_dec(v_pos_785_);
v___x_1330_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__51));
v___x_1331_ = lean_uint32_to_nat(v_all_810_);
v___x_1332_ = l_Nat_reprFast(v___x_1331_);
v___x_1333_ = lean_string_append(v___x_1330_, v___x_1332_);
lean_dec_ref(v___x_1332_);
return v___x_1333_;
}
}
else
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_dec(v_pos_785_);
v___x_1334_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__52));
v___x_1335_ = lean_uint32_to_nat(v_hi13_815_);
v___x_1336_ = l_Nat_reprFast(v___x_1335_);
v___x_1337_ = lean_string_append(v___x_1334_, v___x_1336_);
lean_dec_ref(v___x_1336_);
v___x_1338_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__7));
v___x_1339_ = lean_string_append(v___x_1337_, v___x_1338_);
v___x_1340_ = lean_uint32_to_nat(v_lo13_788_);
v___x_1341_ = l_Nat_reprFast(v___x_1340_);
v___x_1342_ = lean_string_append(v___x_1339_, v___x_1341_);
lean_dec_ref(v___x_1341_);
return v___x_1342_;
}
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
lean_dec(v_pos_785_);
v___x_1343_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__53));
v___x_1344_ = lean_uint32_to_nat(v_hi8_803_);
v___x_1345_ = l_Nat_reprFast(v___x_1344_);
v___x_1346_ = lean_string_append(v___x_1343_, v___x_1345_);
lean_dec_ref(v___x_1345_);
v___x_1347_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Instruction_toString___closed__5));
v___x_1348_ = lean_string_append(v___x_1346_, v___x_1347_);
v___x_1349_ = lean_uint32_to_nat(v_lo18_800_);
v___x_1350_ = l_Nat_reprFast(v___x_1349_);
v___x_1351_ = lean_string_append(v___x_1348_, v___x_1350_);
lean_dec_ref(v___x_1350_);
return v___x_1351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Instruction_toString___boxed(lean_object* v_instr_1352_, lean_object* v_pos_1353_){
_start:
{
uint32_t v_instr_boxed_1354_; lean_object* v_res_1355_; 
v_instr_boxed_1354_ = lean_unbox_uint32(v_instr_1352_);
lean_dec(v_instr_1352_);
v_res_1355_ = l_Lean_Compiler_Bytecode_Instruction_toString(v_instr_boxed_1354_, v_pos_1353_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg(lean_object* v_upperBound_1358_, lean_object* v___x_1359_, lean_object* v_a_1360_, lean_object* v_b_1361_){
_start:
{
uint8_t v___x_1362_; 
v___x_1362_ = lean_nat_dec_lt(v_a_1360_, v_upperBound_1358_);
if (v___x_1362_ == 0)
{
lean_dec(v_a_1360_);
return v_b_1361_;
}
else
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; uint8_t v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; uint8_t v___x_1376_; uint32_t v___x_1377_; uint32_t v___x_1378_; uint32_t v___x_1379_; uint32_t v___x_1380_; uint32_t v___x_1381_; uint32_t v___x_1382_; uint32_t v___x_1383_; uint32_t v___x_1384_; uint32_t v___x_1385_; uint32_t v___x_1386_; uint32_t v___x_1387_; uint32_t v___x_1388_; uint32_t v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1363_ = lean_unsigned_to_nat(4u);
lean_inc(v_a_1360_);
v___x_1364_ = lean_nat_to_int(v_a_1360_);
v___x_1365_ = l_Lean_Compiler_Bytecode_addrToString(v___x_1364_);
lean_dec(v___x_1364_);
v___x_1366_ = lean_nat_mul(v_a_1360_, v___x_1363_);
v___x_1367_ = lean_byte_array_fget(v___x_1359_, v___x_1366_);
v___x_1368_ = lean_unsigned_to_nat(1u);
v___x_1369_ = lean_nat_add(v___x_1366_, v___x_1368_);
v___x_1370_ = lean_byte_array_fget(v___x_1359_, v___x_1369_);
lean_dec(v___x_1369_);
v___x_1371_ = lean_unsigned_to_nat(2u);
v___x_1372_ = lean_nat_add(v___x_1366_, v___x_1371_);
v___x_1373_ = lean_byte_array_fget(v___x_1359_, v___x_1372_);
lean_dec(v___x_1372_);
v___x_1374_ = lean_unsigned_to_nat(3u);
v___x_1375_ = lean_nat_add(v___x_1366_, v___x_1374_);
lean_dec(v___x_1366_);
v___x_1376_ = lean_byte_array_fget(v___x_1359_, v___x_1375_);
lean_dec(v___x_1375_);
v___x_1377_ = lean_uint8_to_uint32(v___x_1367_);
v___x_1378_ = lean_uint8_to_uint32(v___x_1370_);
v___x_1379_ = 8;
v___x_1380_ = lean_uint32_shift_left(v___x_1378_, v___x_1379_);
v___x_1381_ = lean_uint32_lor(v___x_1377_, v___x_1380_);
v___x_1382_ = lean_uint8_to_uint32(v___x_1373_);
v___x_1383_ = 16;
v___x_1384_ = lean_uint32_shift_left(v___x_1382_, v___x_1383_);
v___x_1385_ = lean_uint32_lor(v___x_1381_, v___x_1384_);
v___x_1386_ = lean_uint8_to_uint32(v___x_1376_);
v___x_1387_ = 24;
v___x_1388_ = lean_uint32_shift_left(v___x_1386_, v___x_1387_);
v___x_1389_ = lean_uint32_lor(v___x_1385_, v___x_1388_);
v___x_1390_ = lean_string_append(v_b_1361_, v___x_1365_);
lean_dec_ref(v___x_1365_);
v___x_1391_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___closed__0));
v___x_1392_ = lean_string_append(v___x_1390_, v___x_1391_);
v___x_1393_ = lean_nat_add(v_a_1360_, v___x_1368_);
lean_dec(v_a_1360_);
lean_inc(v___x_1393_);
v___x_1394_ = l_Lean_Compiler_Bytecode_Instruction_toString(v___x_1389_, v___x_1393_);
v___x_1395_ = lean_string_append(v___x_1392_, v___x_1394_);
lean_dec_ref(v___x_1394_);
v___x_1396_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___closed__1));
v___x_1397_ = lean_string_append(v___x_1395_, v___x_1396_);
v_a_1360_ = v___x_1393_;
v_b_1361_ = v___x_1397_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___boxed(lean_object* v_upperBound_1399_, lean_object* v___x_1400_, lean_object* v_a_1401_, lean_object* v_b_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg(v_upperBound_1399_, v___x_1400_, v_a_1401_, v_b_1402_);
lean_dec_ref(v___x_1400_);
lean_dec(v_upperBound_1399_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1___redArg(lean_object* v_upperBound_1404_, lean_object* v___x_1405_, lean_object* v_a_1406_, lean_object* v_b_1407_){
_start:
{
uint8_t v___x_1408_; 
v___x_1408_ = lean_nat_dec_lt(v_a_1406_, v_upperBound_1404_);
if (v___x_1408_ == 0)
{
lean_dec(v_a_1406_);
return v_b_1407_;
}
else
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; uint32_t v___x_1423_; uint32_t v___x_1424_; uint32_t v___x_1425_; uint32_t v___x_1426_; uint32_t v___x_1427_; uint32_t v___x_1428_; uint32_t v___x_1429_; uint32_t v___x_1430_; uint32_t v___x_1431_; uint32_t v___x_1432_; uint32_t v___x_1433_; uint32_t v___x_1434_; uint32_t v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1409_ = lean_unsigned_to_nat(4u);
lean_inc(v_a_1406_);
v___x_1410_ = lean_nat_to_int(v_a_1406_);
v___x_1411_ = l_Lean_Compiler_Bytecode_addrToString(v___x_1410_);
lean_dec(v___x_1410_);
v___x_1412_ = lean_nat_mul(v_a_1406_, v___x_1409_);
v___x_1413_ = lean_byte_array_fget(v___x_1405_, v___x_1412_);
v___x_1414_ = lean_unsigned_to_nat(1u);
v___x_1415_ = lean_nat_add(v___x_1412_, v___x_1414_);
v___x_1416_ = lean_byte_array_fget(v___x_1405_, v___x_1415_);
lean_dec(v___x_1415_);
v___x_1417_ = lean_unsigned_to_nat(2u);
v___x_1418_ = lean_nat_add(v___x_1412_, v___x_1417_);
v___x_1419_ = lean_byte_array_fget(v___x_1405_, v___x_1418_);
lean_dec(v___x_1418_);
v___x_1420_ = lean_unsigned_to_nat(3u);
v___x_1421_ = lean_nat_add(v___x_1412_, v___x_1420_);
lean_dec(v___x_1412_);
v___x_1422_ = lean_byte_array_fget(v___x_1405_, v___x_1421_);
lean_dec(v___x_1421_);
v___x_1423_ = lean_uint8_to_uint32(v___x_1413_);
v___x_1424_ = lean_uint8_to_uint32(v___x_1416_);
v___x_1425_ = 8;
v___x_1426_ = lean_uint32_shift_left(v___x_1424_, v___x_1425_);
v___x_1427_ = lean_uint32_lor(v___x_1423_, v___x_1426_);
v___x_1428_ = lean_uint8_to_uint32(v___x_1419_);
v___x_1429_ = 16;
v___x_1430_ = lean_uint32_shift_left(v___x_1428_, v___x_1429_);
v___x_1431_ = lean_uint32_lor(v___x_1427_, v___x_1430_);
v___x_1432_ = lean_uint8_to_uint32(v___x_1422_);
v___x_1433_ = 24;
v___x_1434_ = lean_uint32_shift_left(v___x_1432_, v___x_1433_);
v___x_1435_ = lean_uint32_lor(v___x_1431_, v___x_1434_);
v___x_1436_ = lean_string_append(v_b_1407_, v___x_1411_);
lean_dec_ref(v___x_1411_);
v___x_1437_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___closed__0));
v___x_1438_ = lean_string_append(v___x_1436_, v___x_1437_);
v___x_1439_ = lean_nat_add(v_a_1406_, v___x_1414_);
lean_dec(v_a_1406_);
lean_inc(v___x_1439_);
v___x_1440_ = l_Lean_Compiler_Bytecode_Instruction_toString(v___x_1435_, v___x_1439_);
v___x_1441_ = lean_string_append(v___x_1438_, v___x_1440_);
lean_dec_ref(v___x_1440_);
v___x_1442_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___closed__1));
v___x_1443_ = lean_string_append(v___x_1441_, v___x_1442_);
v___x_1444_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg(v_upperBound_1404_, v___x_1405_, v___x_1439_, v___x_1443_);
return v___x_1444_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1___redArg___boxed(lean_object* v_upperBound_1445_, lean_object* v___x_1446_, lean_object* v_a_1447_, lean_object* v_b_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1___redArg(v_upperBound_1445_, v___x_1446_, v_a_1447_, v_b_1448_);
lean_dec_ref(v___x_1446_);
lean_dec(v_upperBound_1445_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___redArg(lean_object* v_upperBound_1451_, lean_object* v___x_1452_, lean_object* v_a_1453_, lean_object* v_b_1454_){
_start:
{
uint8_t v___x_1455_; 
v___x_1455_ = lean_nat_dec_lt(v_a_1453_, v_upperBound_1451_);
if (v___x_1455_ == 0)
{
lean_dec(v_a_1453_);
return v_b_1454_;
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1456_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___redArg___closed__0));
v___x_1457_ = lean_string_append(v_b_1454_, v___x_1456_);
lean_inc(v_a_1453_);
v___x_1458_ = l_Nat_reprFast(v_a_1453_);
v___x_1459_ = lean_string_append(v___x_1457_, v___x_1458_);
lean_dec_ref(v___x_1458_);
v___x_1460_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___closed__0));
v___x_1461_ = lean_string_append(v___x_1459_, v___x_1460_);
v___x_1462_ = lean_array_fget_borrowed(v___x_1452_, v_a_1453_);
lean_inc(v___x_1462_);
v___x_1463_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1462_, v___x_1455_);
v___x_1464_ = lean_string_append(v___x_1461_, v___x_1463_);
lean_dec_ref(v___x_1463_);
v___x_1465_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg___closed__1));
v___x_1466_ = lean_string_append(v___x_1464_, v___x_1465_);
v___x_1467_ = lean_unsigned_to_nat(1u);
v___x_1468_ = lean_nat_add(v_a_1453_, v___x_1467_);
lean_dec(v_a_1453_);
v_a_1453_ = v___x_1468_;
v_b_1454_ = v___x_1466_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___redArg___boxed(lean_object* v_upperBound_1470_, lean_object* v___x_1471_, lean_object* v_a_1472_, lean_object* v_b_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___redArg(v_upperBound_1470_, v___x_1471_, v_a_1472_, v_b_1473_);
lean_dec_ref(v___x_1471_);
lean_dec(v_upperBound_1470_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_disassemble(lean_object* v_code_1482_){
_start:
{
lean_object* v_name_1483_; lean_object* v_code_1484_; lean_object* v_stackReserved_1485_; lean_object* v_stackSpace_1486_; lean_object* v_symbols_1487_; lean_object* v_arity_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v_sz_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; uint8_t v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v_str_1510_; lean_object* v___x_1511_; lean_object* v_str_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; uint8_t v___x_1515_; 
v_name_1483_ = lean_ctor_get(v_code_1482_, 0);
lean_inc(v_name_1483_);
v_code_1484_ = lean_ctor_get(v_code_1482_, 1);
lean_inc_ref(v_code_1484_);
v_stackReserved_1485_ = lean_ctor_get(v_code_1482_, 2);
lean_inc(v_stackReserved_1485_);
v_stackSpace_1486_ = lean_ctor_get(v_code_1482_, 3);
lean_inc(v_stackSpace_1486_);
v_symbols_1487_ = lean_ctor_get(v_code_1482_, 4);
lean_inc_ref(v_symbols_1487_);
v_arity_1488_ = lean_ctor_get(v_code_1482_, 5);
lean_inc(v_arity_1488_);
lean_dec_ref(v_code_1482_);
v___x_1489_ = lean_byte_array_size(v_code_1484_);
v___x_1490_ = lean_unsigned_to_nat(2u);
v_sz_1491_ = lean_nat_shiftr(v___x_1489_, v___x_1490_);
v___x_1492_ = lean_unsigned_to_nat(0u);
v___x_1493_ = ((lean_object*)(l_Lean_Compiler_Bytecode_disassemble___closed__0));
v___x_1494_ = 1;
v___x_1495_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1483_, v___x_1494_);
v___x_1496_ = lean_string_append(v___x_1493_, v___x_1495_);
lean_dec_ref(v___x_1495_);
v___x_1497_ = ((lean_object*)(l_Lean_Compiler_Bytecode_disassemble___closed__1));
v___x_1498_ = lean_string_append(v___x_1496_, v___x_1497_);
v___x_1499_ = l_Nat_reprFast(v_arity_1488_);
v___x_1500_ = lean_string_append(v___x_1498_, v___x_1499_);
lean_dec_ref(v___x_1499_);
v___x_1501_ = ((lean_object*)(l_Lean_Compiler_Bytecode_disassemble___closed__2));
v___x_1502_ = lean_string_append(v___x_1500_, v___x_1501_);
v___x_1503_ = l_Nat_reprFast(v_stackSpace_1486_);
v___x_1504_ = lean_string_append(v___x_1502_, v___x_1503_);
lean_dec_ref(v___x_1503_);
v___x_1505_ = ((lean_object*)(l_Lean_Compiler_Bytecode_disassemble___closed__3));
v___x_1506_ = lean_string_append(v___x_1504_, v___x_1505_);
v___x_1507_ = l_Nat_reprFast(v_stackReserved_1485_);
v___x_1508_ = lean_string_append(v___x_1506_, v___x_1507_);
lean_dec_ref(v___x_1507_);
v___x_1509_ = ((lean_object*)(l_Lean_Compiler_Bytecode_disassemble___closed__4));
v_str_1510_ = lean_string_append(v___x_1508_, v___x_1509_);
v___x_1511_ = ((lean_object*)(l_Lean_Compiler_Bytecode_disassemble___closed__5));
v_str_1512_ = lean_string_append(v_str_1510_, v___x_1511_);
v___x_1513_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1___redArg(v_sz_1491_, v_code_1484_, v___x_1492_, v_str_1512_);
lean_dec_ref(v_code_1484_);
lean_dec(v_sz_1491_);
v___x_1514_ = lean_array_get_size(v_symbols_1487_);
v___x_1515_ = lean_nat_dec_eq(v___x_1514_, v___x_1492_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1516_ = ((lean_object*)(l_Lean_Compiler_Bytecode_disassemble___closed__6));
v___x_1517_ = lean_string_append(v___x_1513_, v___x_1516_);
v___x_1518_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___redArg(v___x_1514_, v_symbols_1487_, v___x_1492_, v___x_1517_);
lean_dec_ref(v_symbols_1487_);
return v___x_1518_;
}
else
{
lean_dec_ref(v_symbols_1487_);
return v___x_1513_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0(lean_object* v_upperBound_1519_, lean_object* v___x_1520_, lean_object* v_inst_1521_, lean_object* v_R_1522_, lean_object* v_a_1523_, lean_object* v_b_1524_, lean_object* v_c_1525_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___redArg(v_upperBound_1519_, v___x_1520_, v_a_1523_, v_b_1524_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0___boxed(lean_object* v_upperBound_1527_, lean_object* v___x_1528_, lean_object* v_inst_1529_, lean_object* v_R_1530_, lean_object* v_a_1531_, lean_object* v_b_1532_, lean_object* v_c_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__0(v_upperBound_1527_, v___x_1528_, v_inst_1529_, v_R_1530_, v_a_1531_, v_b_1532_, v_c_1533_);
lean_dec_ref(v___x_1528_);
lean_dec(v_upperBound_1527_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1(lean_object* v_upperBound_1535_, lean_object* v___x_1536_, lean_object* v_inst_1537_, lean_object* v_R_1538_, lean_object* v_a_1539_, lean_object* v_b_1540_, lean_object* v_c_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1___redArg(v_upperBound_1535_, v___x_1536_, v_a_1539_, v_b_1540_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1___boxed(lean_object* v_upperBound_1543_, lean_object* v___x_1544_, lean_object* v_inst_1545_, lean_object* v_R_1546_, lean_object* v_a_1547_, lean_object* v_b_1548_, lean_object* v_c_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1(v_upperBound_1543_, v___x_1544_, v_inst_1545_, v_R_1546_, v_a_1547_, v_b_1548_, v_c_1549_);
lean_dec_ref(v___x_1544_);
lean_dec(v_upperBound_1543_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1(lean_object* v_upperBound_1551_, lean_object* v___x_1552_, lean_object* v_inst_1553_, lean_object* v_R_1554_, lean_object* v_a_1555_, lean_object* v_b_1556_, lean_object* v_c_1557_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___redArg(v_upperBound_1551_, v___x_1552_, v_a_1555_, v_b_1556_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1___boxed(lean_object* v_upperBound_1559_, lean_object* v___x_1560_, lean_object* v_inst_1561_, lean_object* v_R_1562_, lean_object* v_a_1563_, lean_object* v_b_1564_, lean_object* v_c_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_Bytecode_disassemble_spec__1_spec__1(v_upperBound_1559_, v___x_1560_, v_inst_1561_, v_R_1562_, v_a_1563_, v_b_1564_, v_c_1565_);
lean_dec_ref(v___x_1560_);
lean_dec(v_upperBound_1559_);
return v_res_1566_;
}
}
lean_object* runtime_initialize_Lean_Compiler_Bytecode_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_Bytecode_Instruction(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_Bytecode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_Bytecode_instInhabitedInstruction_default = _init_l_Lean_Compiler_Bytecode_instInhabitedInstruction_default();
l_Lean_Compiler_Bytecode_instInhabitedInstruction = _init_l_Lean_Compiler_Bytecode_instInhabitedInstruction();
l_Lean_Compiler_Bytecode_maxUConst = _init_l_Lean_Compiler_Bytecode_maxUConst();
lean_mark_persistent(l_Lean_Compiler_Bytecode_maxUConst);
l_Lean_Compiler_Bytecode_maxNConst = _init_l_Lean_Compiler_Bytecode_maxNConst();
lean_mark_persistent(l_Lean_Compiler_Bytecode_maxNConst);
l_Lean_Compiler_Bytecode_Instruction_nojump = _init_l_Lean_Compiler_Bytecode_Instruction_nojump();
l_Lean_Compiler_Bytecode_addrToString___boxed__const__1 = _init_l_Lean_Compiler_Bytecode_addrToString___boxed__const__1();
lean_mark_persistent(l_Lean_Compiler_Bytecode_addrToString___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_Bytecode_Instruction(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_Bytecode_Basic(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Bytecode_Instruction(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_Bytecode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Bytecode_Instruction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_Bytecode_Instruction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_Bytecode_Instruction(builtin);
}
#ifdef __cplusplus
}
#endif
