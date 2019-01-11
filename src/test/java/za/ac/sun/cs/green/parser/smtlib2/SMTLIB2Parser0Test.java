package za.ac.sun.cs.green.parser.smtlib2;

import static org.junit.Assert.*;

import java.util.logging.Level;
import java.util.logging.Logger;

import org.junit.BeforeClass;
import org.junit.Test;

import za.ac.sun.cs.green.util.NullLogger;

public class SMTLIB2Parser0Test {

	private static final boolean DO_LOG = false;
	
	private static Logger log;

	@BeforeClass
	public static void setupLog() {
		if (DO_LOG) {
			log = Logger.getLogger("za.ac.sun.cs.green[JUnit4]");
			log.setUseParentHandlers(false);
			log.setLevel(Level.ALL);
//			log.addHandler(new GreenHandler(Level.ALL));
		} else {
			log = new NullLogger();
		}
	}

	@Test
	public void test01() throws ParseException {
		Scanner0 s = new Scanner0("(set-logic QF_AUFBV)"
				+ "(set-info :status unknown)"
				+ "(get-info :name)"
				+ "(get-info :version)"
				+ "(set-option :produce-models true)"
				+ "(declare-fun |__ESBMC_ptr_obj_start_0| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x1 (= |__ESBMC_ptr_obj_start_0| (_ bv0 32))))"
				+ "?x1))"
				+ "(assert"
				+ "(let ((?x2 (= |__ESBMC_ptr_obj_start_0| (_ bv0 32))))"
				+ "?x2))"
				+ "(declare-fun |__ESBMC_ptr_obj_start_1| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x3 (= |__ESBMC_ptr_obj_start_1| (_ bv1 32))))"
				+ "?x3))"
				+ "(declare-fun |__ESBMC_ptr_obj_end_1| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x4 (= |__ESBMC_ptr_obj_end_1| (_ bv4294967295 32))))"
				+ "?x4))"
				+ "(declare-fun |__ESBMC_ptr_obj_end_0| () (_ BitVec 32))"
				+ "(declare-fun |smt_conv::tuple_create::0.start| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x5 (= |smt_conv::tuple_create::0.start| |__ESBMC_ptr_obj_start_0|)))"
				+ "?x5))"
				+ "(declare-fun |smt_conv::tuple_create::0.end| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x6 (= |smt_conv::tuple_create::0.end| |__ESBMC_ptr_obj_end_0|)))"
				+ "?x6))"
				+ "(declare-fun |smt_conv::tuple_create::1.start| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x7 (= |smt_conv::tuple_create::1.start| |__ESBMC_ptr_obj_start_0|)))"
				+ "?x7))"
				+ "(declare-fun |smt_conv::tuple_create::1.end| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x8 (= |smt_conv::tuple_create::1.end| |__ESBMC_ptr_obj_end_0|)))"
				+ "?x8))"
				+ "(declare-fun |__ESBMC_ptr_addr_range_0.start| () (_ BitVec 32))"
				+ "(declare-fun |__ESBMC_ptr_addr_range_0.end| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x9 (= |smt_conv::tuple_create::1.start| |__ESBMC_ptr_addr_range_0.start|)))"
				+ "(let ((?x10 (= |smt_conv::tuple_create::1.end| |__ESBMC_ptr_addr_range_0.end|)))"
				+ "(let ((?x11 (and ?x9 ?x10)))"
				+ "?x11))))"
				+ "(declare-fun |smt_conv::tuple_create::2.start| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x12 (= |smt_conv::tuple_create::2.start| |__ESBMC_ptr_obj_start_1|)))"
				+ "?x12))"
				+ "(declare-fun |smt_conv::tuple_create::2.end| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x13 (= |smt_conv::tuple_create::2.end| |__ESBMC_ptr_obj_end_1|)))"
				+ "?x13))"
				+ "(declare-fun |smt_conv::tuple_create::3.start| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x14 (= |smt_conv::tuple_create::3.start| |__ESBMC_ptr_obj_start_1|)))"
				+ "?x14))"
				+ "(declare-fun |smt_conv::tuple_create::3.end| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x15 (= |smt_conv::tuple_create::3.end| |__ESBMC_ptr_obj_end_1|)))"
				+ "?x15))"
				+ "(declare-fun |__ESBMC_ptr_addr_range_1.start| () (_ BitVec 32))"
				+ "(declare-fun |__ESBMC_ptr_addr_range_1.end| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x16 (= |smt_conv::tuple_create::3.start| |__ESBMC_ptr_addr_range_1.start|)))"
				+ "(let ((?x17 (= |smt_conv::tuple_create::3.end| |__ESBMC_ptr_addr_range_1.end|)))"
				+ "(let ((?x18 (and ?x16 ?x17)))"
				+ "?x18))))"
				+ "(declare-fun |smt_conv::tuple_create::4.start| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x19 (= |smt_conv::tuple_create::4.start| |__ESBMC_ptr_obj_start_0|)))"
				+ "?x19))"
				+ "(declare-fun |smt_conv::tuple_create::4.end| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x20 (= |smt_conv::tuple_create::4.end| |__ESBMC_ptr_obj_end_0|)))"
				+ "?x20))"
				+ "(declare-fun |__ESBMC_addrspace_arr_1[]start| () (Array (_ BitVec 32) (_ BitVec 32)))"
				+ "(declare-fun |smt_conv::tuple_array_update::0.start| () (Array (_ BitVec 32) (_ BitVec 32)))"
				+ "(declare-fun |__ESBMC_addrspace_arr_1[]end| () (Array (_ BitVec 32) (_ BitVec 32)))"
				+ "(declare-fun |smt_conv::tuple_array_update::0.end| () (Array (_ BitVec 32) (_ BitVec 32)))"
				+ "(assert"
				+ "(let ((?x21 (store |__ESBMC_addrspace_arr_1[]start| (_ bv0 32) |smt_conv::tuple_create::4.start|)))"
				+ "(let ((?x22 (= |smt_conv::tuple_array_update::0.start| ?x21)))"
				+ "(let ((?x23 (store |__ESBMC_addrspace_arr_1[]end| (_ bv0 32) |smt_conv::tuple_create::4.end|)))"
				+ "(let ((?x24 (= |smt_conv::tuple_array_update::0.end| ?x23)))"
				+ "(let ((?x25 (and ?x22 ?x24)))"
				+ "?x25))))))"
				+ "(declare-fun |__ESBMC_addrspace_arr_2[]start| () (Array (_ BitVec 32) (_ BitVec 32)))"
				+ "(declare-fun |__ESBMC_addrspace_arr_2[]end| () (Array (_ BitVec 32) (_ BitVec 32)))"
				+ "(assert"
				+ "(let ((?x26 (= |__ESBMC_addrspace_arr_2[]start| |smt_conv::tuple_array_update::0.start|)))"
				+ "(let ((?x27 (= |__ESBMC_addrspace_arr_2[]end| |smt_conv::tuple_array_update::0.end|)))"
				+ "(let ((?x28 (and ?x26 ?x27)))"
				+ "?x28))))"
				+ "(declare-fun |smt_conv::tuple_create::5.start| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x29 (= |smt_conv::tuple_create::5.start| |__ESBMC_ptr_obj_start_1|)))"
				+ "?x29))"
				+ "(declare-fun |smt_conv::tuple_create::5.end| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x30 (= |smt_conv::tuple_create::5.end| |__ESBMC_ptr_obj_end_1|)))"
				+ "?x30))"
				+ "(declare-fun |smt_conv::tuple_array_update::1.start| () (Array (_ BitVec 32) (_ BitVec 32)))"
				+ "(declare-fun |smt_conv::tuple_array_update::1.end| () (Array (_ BitVec 32) (_ BitVec 32)))"
				+ "(assert"
				+ "(let ((?x31 (store |__ESBMC_addrspace_arr_2[]start| (_ bv1 32) |smt_conv::tuple_create::5.start|)))"
				+ "(let ((?x32 (= |smt_conv::tuple_array_update::1.start| ?x31)))"
				+ "(let ((?x33 (store |__ESBMC_addrspace_arr_2[]end| (_ bv1 32) |smt_conv::tuple_create::5.end|)))"
				+ "(let ((?x34 (= |smt_conv::tuple_array_update::1.end| ?x33)))"
				+ "(let ((?x35 (and ?x32 ?x34)))"
				+ "?x35))))))"
				+ "(declare-fun |__ESBMC_addrspace_arr_3[]start| () (Array (_ BitVec 32) (_ BitVec 32)))"
				+ "(declare-fun |__ESBMC_addrspace_arr_3[]end| () (Array (_ BitVec 32) (_ BitVec 32)))"
				+ "(assert"
				+ "(let ((?x36 (= |__ESBMC_addrspace_arr_3[]start| |smt_conv::tuple_array_update::1.start|)))"
				+ "(let ((?x37 (= |__ESBMC_addrspace_arr_3[]end| |smt_conv::tuple_array_update::1.end|)))"
				+ "(let ((?x38 (and ?x36 ?x37)))"
				+ "?x38))))"
				+ "(declare-fun |smt_conv::tuple_create::6.pointer_object| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x39 (= |smt_conv::tuple_create::6.pointer_object| (_ bv0 32))))"
				+ "?x39))"
				+ "(declare-fun |smt_conv::tuple_create::6.pointer_offset| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x40 (= |smt_conv::tuple_create::6.pointer_offset| (_ bv0 32))))"
				+ "?x40))"
				+ "(declare-fun |smt_conv::tuple_create::7.pointer_object| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x41 (= |smt_conv::tuple_create::7.pointer_object| (_ bv0 32))))"
				+ "?x41))"
				+ "(declare-fun |smt_conv::tuple_create::7.pointer_offset| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x42 (= |smt_conv::tuple_create::7.pointer_offset| (_ bv0 32))))"
				+ "?x42))"
				+ "(declare-fun |0.pointer_object| () (_ BitVec 32))"
				+ "(declare-fun |0.pointer_offset| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x43 (= |0.pointer_object| |smt_conv::tuple_create::7.pointer_object|)))"
				+ "(let ((?x44 (= |0.pointer_offset| |smt_conv::tuple_create::7.pointer_offset|)))"
				+ "(let ((?x45 (and ?x43 ?x44)))"
				+ "?x45))))"
				+ "(declare-fun |smt_conv::tuple_create::8.pointer_object| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x46 (= |smt_conv::tuple_create::8.pointer_object| (_ bv0 32))))"
				+ "?x46))"
				+ "(declare-fun |smt_conv::tuple_create::8.pointer_offset| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x47 (= |smt_conv::tuple_create::8.pointer_offset| (_ bv0 32))))"
				+ "?x47))"
				+ "(declare-fun |smt_conv::tuple_create::9.pointer_object| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x48 (= |smt_conv::tuple_create::9.pointer_object| (_ bv0 32))))"
				+ "?x48))"
				+ "(declare-fun |smt_conv::tuple_create::9.pointer_offset| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x49 (= |smt_conv::tuple_create::9.pointer_offset| (_ bv0 32))))"
				+ "?x49))"
				+ "(declare-fun |NULL.pointer_object| () (_ BitVec 32))"
				+ "(declare-fun |NULL.pointer_offset| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x50 (= |NULL.pointer_object| |smt_conv::tuple_create::9.pointer_object|)))"
				+ "(let ((?x51 (= |NULL.pointer_offset| |smt_conv::tuple_create::9.pointer_offset|)))"
				+ "(let ((?x52 (and ?x50 ?x51)))"
				+ "?x52))))"
				+ "(declare-fun |smt_conv::tuple_create::10.pointer_object| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x53 (= |smt_conv::tuple_create::10.pointer_object| (_ bv1 32))))"
				+ "?x53))"
				+ "(declare-fun |smt_conv::tuple_create::10.pointer_offset| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x54 (= |smt_conv::tuple_create::10.pointer_offset| (_ bv0 32))))"
				+ "?x54))"
				+ "(declare-fun |smt_conv::tuple_create::11.pointer_object| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x55 (= |smt_conv::tuple_create::11.pointer_object| (_ bv1 32))))"
				+ "?x55))"
				+ "(declare-fun |smt_conv::tuple_create::11.pointer_offset| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x56 (= |smt_conv::tuple_create::11.pointer_offset| (_ bv0 32))))"
				+ "?x56))"
				+ "(declare-fun |INVALID.pointer_object| () (_ BitVec 32))"
				+ "(declare-fun |INVALID.pointer_offset| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x57 (= |INVALID.pointer_object| |smt_conv::tuple_create::11.pointer_object|)))"
				+ "(let ((?x58 (= |INVALID.pointer_offset| |smt_conv::tuple_create::11.pointer_offset|)))"
				+ "(let ((?x59 (and ?x57 ?x58)))"
				+ "?x59))))"
				+ "(push 1)"
				+ "(declare-fun |c::pthread_lib::num_total_threads&0#1| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x60 (= |c::pthread_lib::num_total_threads&0#1| (_ bv0 32))))"
				+ "?x60))"
				+ "(declare-fun |c::pthread_lib::num_threads_running&0#1| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x61 (= |c::pthread_lib::num_threads_running&0#1| (_ bv0 32))))"
				+ "?x61))"
				+ "(declare-fun |c::__ESBMC_alloc&0#1| () (Array (_ BitVec 32) (_ BitVec 1)))"
				+ "(declare-fun |smt_conv::inf_array0| () (Array (_ BitVec 32) (_ BitVec 1)))"
				+ "(assert"
				+ "(let ((?x62 (= |c::__ESBMC_alloc&0#1| |smt_conv::inf_array0|)))"
				+ "?x62))"
				+ "(declare-fun |c::__ESBMC_deallocated&0#1| () (Array (_ BitVec 32) (_ BitVec 1)))"
				+ "(declare-fun |smt_conv::inf_array1| () (Array (_ BitVec 32) (_ BitVec 1)))"
				+ "(assert"
				+ "(let ((?x63 (= |c::__ESBMC_deallocated&0#1| |smt_conv::inf_array1|)))"
				+ "?x63))"
				+ "(declare-fun |c::__ESBMC_is_dynamic&0#1| () (Array (_ BitVec 32) (_ BitVec 1)))"
				+ "(declare-fun |smt_conv::inf_array2| () (Array (_ BitVec 32) (_ BitVec 1)))"
				+ "(assert"
				+ "(let ((?x64 (= |c::__ESBMC_is_dynamic&0#1| |smt_conv::inf_array2|)))"
				+ "?x64))"
				+ "(declare-fun |c::__ESBMC_alloc_size&0#1| () (Array (_ BitVec 32) (_ BitVec 32)))"
				+ "(declare-fun |smt_conv::inf_array3| () (Array (_ BitVec 32) (_ BitVec 32)))"
				+ "(assert"
				+ "(let ((?x65 (= |c::__ESBMC_alloc_size&0#1| |smt_conv::inf_array3|)))"
				+ "?x65))"
				+ "(declare-fun |c::__PRETTY_FUNCTION__&0#1.pointer_object| () (_ BitVec 32))"
				+ "(declare-fun |c::__PRETTY_FUNCTION__&0#1.pointer_offset| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x66 (= |c::__PRETTY_FUNCTION__&0#1.pointer_object| |NULL.pointer_object|)))"
				+ "(let ((?x67 (= |c::__PRETTY_FUNCTION__&0#1.pointer_offset| |NULL.pointer_offset|)))"
				+ "(let ((?x68 (and ?x66 ?x67)))"
				+ "?x68))))"
				+ "(declare-fun |smt_conv::tuple_create::12.pointer_object| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x69 (= |smt_conv::tuple_create::12.pointer_object| (_ bv2 32))))"
				+ "?x69))"
				+ "(declare-fun |smt_conv::tuple_create::12.pointer_offset| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x70 (= |smt_conv::tuple_create::12.pointer_offset| (_ bv0 32))))"
				+ "?x70))"
				+ "(declare-fun |__ESBMC_ptr_obj_start_2| () (_ BitVec 32))"
				+ "(declare-fun |__ESBMC_ptr_obj_end_2| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x71 (bvadd |__ESBMC_ptr_obj_start_2| (_ bv1 32))))"
				+ "(let ((?x72 (= ?x71 |__ESBMC_ptr_obj_end_2|)))"
				+ "?x72)))"
				+ "(assert"
				+ "(let ((?x73 (= (_ bv0 32) (_ bv1 32))))"
				+ "(let ((?x74 (bvugt |__ESBMC_ptr_obj_end_2| |__ESBMC_ptr_obj_start_2|)))"
				+ "(let ((?x75 (or ?x73 ?x74)))"
				+ "?x75))))"
				+ "(assert"
				+ "(let ((?x76 (bvult |__ESBMC_ptr_obj_end_2| |__ESBMC_ptr_obj_start_0|)))"
				+ "(let ((?x77 (bvugt |__ESBMC_ptr_obj_start_2| |__ESBMC_ptr_obj_end_0|)))"
				+ "(let ((?x78 (or ?x76 ?x77)))"
				+ "?x78))))"
				+ "(declare-fun |smt_conv::tuple_create::13.start| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x79 (= |smt_conv::tuple_create::13.start| |__ESBMC_ptr_obj_start_2|)))"
				+ "?x79))"
				+ "(declare-fun |smt_conv::tuple_create::13.end| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x80 (= |smt_conv::tuple_create::13.end| |__ESBMC_ptr_obj_end_2|)))"
				+ "?x80))"
				+ "(declare-fun |smt_conv::tuple_create::14.start| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x81 (= |smt_conv::tuple_create::14.start| |__ESBMC_ptr_obj_start_2|)))"
				+ "?x81))"
				+ "(declare-fun |smt_conv::tuple_create::14.end| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x82 (= |smt_conv::tuple_create::14.end| |__ESBMC_ptr_obj_end_2|)))"
				+ "?x82))"
				+ "(declare-fun |__ESBMC_ptr_addr_range_2.start| () (_ BitVec 32))"
				+ "(declare-fun |__ESBMC_ptr_addr_range_2.end| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x83 (= |__ESBMC_ptr_addr_range_2.start| |smt_conv::tuple_create::14.start|)))"
				+ "(let ((?x84 (= |__ESBMC_ptr_addr_range_2.end| |smt_conv::tuple_create::14.end|)))"
				+ "(let ((?x85 (and ?x83 ?x84)))"
				+ "?x85))))"
				+ "(declare-fun |smt_conv::tuple_create::15.start| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x86 (= |smt_conv::tuple_create::15.start| |__ESBMC_ptr_obj_start_2|)))"
				+ "?x86))"
				+ "(declare-fun |smt_conv::tuple_create::15.end| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x87 (= |smt_conv::tuple_create::15.end| |__ESBMC_ptr_obj_end_2|)))"
				+ "?x87))"
				+ "(declare-fun |smt_conv::tuple_array_update::2.start| () (Array (_ BitVec 32) (_ BitVec 32)))"
				+ "(declare-fun |smt_conv::tuple_array_update::2.end| () (Array (_ BitVec 32) (_ BitVec 32)))"
				+ "(assert"
				+ "(let ((?x88 (store |__ESBMC_addrspace_arr_3[]start| (_ bv2 32) |smt_conv::tuple_create::15.start|)))"
				+ "(let ((?x89 (= |smt_conv::tuple_array_update::2.start| ?x88)))"
				+ "(let ((?x90 (store |__ESBMC_addrspace_arr_3[]end| (_ bv2 32) |smt_conv::tuple_create::15.end|)))"
				+ "(let ((?x91 (= |smt_conv::tuple_array_update::2.end| ?x90)))"
				+ "(let ((?x92 (and ?x89 ?x91)))"
				+ "?x92))))))"
				+ "(declare-fun |__ESBMC_addrspace_arr_4[]start| () (Array (_ BitVec 32) (_ BitVec 32)))"
				+ "(declare-fun |__ESBMC_addrspace_arr_4[]end| () (Array (_ BitVec 32) (_ BitVec 32)))"
				+ "(assert"
				+ "(let ((?x93 (= |__ESBMC_addrspace_arr_4[]start| |smt_conv::tuple_array_update::2.start|)))"
				+ "(let ((?x94 (= |__ESBMC_addrspace_arr_4[]end| |smt_conv::tuple_array_update::2.end|)))"
				+ "(let ((?x95 (and ?x93 ?x94)))"
				+ "?x95))))"
				+ "(assert"
				+ "(let ((?x96 (select |c::__ESBMC_is_dynamic&0#1| (_ bv2 32))))"
				+ "(let ((?x97 (= ?x96 (_ bv1 1))))"
				+ "(let ((?x98 (= ?x97 false)))"
				+ "?x98))))"
				+ "(declare-fun |address_of_str_const().pointer_object| () (_ BitVec 32))"
				+ "(declare-fun |address_of_str_const().pointer_offset| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x99 (= |address_of_str_const().pointer_object| |smt_conv::tuple_create::12.pointer_object|)))"
				+ "(let ((?x100 (= |address_of_str_const().pointer_offset| |smt_conv::tuple_create::12.pointer_offset|)))"
				+ "(let ((?x101 (and ?x99 ?x100)))"
				+ "?x101))))"
				+ "(declare-fun |smt_conv::tuple_update::0.pointer_object| () (_ BitVec 32))"
				+ "(declare-fun |smt_conv::tuple_update::0.pointer_offset| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x102 (= |address_of_str_const().pointer_object| |smt_conv::tuple_update::0.pointer_object|)))"
				+ "(let ((?x103 (= |smt_conv::tuple_update::0.pointer_offset| (_ bv0 32))))"
				+ "(let ((?x104 (and ?x102 ?x103)))"
				+ "?x104))))"
				+ "(declare-fun |smt_conv::tuple_update::1.pointer_object| () (_ BitVec 32))"
				+ "(declare-fun |smt_conv::tuple_update::1.pointer_offset| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x105 (= |address_of_str_const().pointer_object| |smt_conv::tuple_update::1.pointer_object|)))"
				+ "(let ((?x106 (= |smt_conv::tuple_update::1.pointer_offset| (_ bv0 32))))"
				+ "(let ((?x107 (and ?x105 ?x106)))"
				+ "?x107))))"
				+ "(declare-fun |c::__FILE__&0#1.pointer_object| () (_ BitVec 32))"
				+ "(declare-fun |c::__FILE__&0#1.pointer_offset| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x108 (= |c::__FILE__&0#1.pointer_object| |smt_conv::tuple_update::1.pointer_object|)))"
				+ "(let ((?x109 (= |c::__FILE__&0#1.pointer_offset| |smt_conv::tuple_update::1.pointer_offset|)))"
				+ "(let ((?x110 (and ?x108 ?x109)))"
				+ "?x110))))"
				+ "(declare-fun |c::__LINE__&0#1| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x111 (= |c::__LINE__&0#1| (_ bv0 32))))"
				+ "?x111))"
				+ "(declare-fun |c::pthread_lib::num_total_threads&0#2| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x112 (= |c::pthread_lib::num_total_threads&0#2| (_ bv1 32))))"
				+ "?x112))"
				+ "(declare-fun |c::pthread_lib::num_threads_running&0#2| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x113 (= |c::pthread_lib::num_threads_running&0#2| (_ bv1 32))))"
				+ "?x113))"
				+ "(declare-fun |c::main::$tmp::return_value_nondet_int$1@1!0&0#1| () (_ BitVec 32))"
				+ "(declare-fun |nondet$symex::nondet0| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x114 (= |c::main::$tmp::return_value_nondet_int$1@1!0&0#1| |nondet$symex::nondet0|)))"
				+ "?x114))"
				+ "(declare-fun |c::jaja::main::1::k@1!0&0#1| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x115 (= |c::jaja::main::1::k@1!0&0#1| |c::main::$tmp::return_value_nondet_int$1@1!0&0#1|)))"
				+ "?x115))"
				+ "(declare-fun |c::jaja::main::1::i@1!0&0#1| () (_ BitVec 32))"
				+ "(assert"
				+ "(let ((?x116 (= |c::jaja::main::1::i@1!0&0#1| (_ bv0 32))))"
				+ "?x116))"
				+ "(push 1)"
				+ "(assert true)"
				+ "(assert"
				+ "(let ((?x117 (= |c::jaja::main::1::i@1!0&0#1| (_ bv0 32))))"
				+ "?x117))"
				+ "(push 1)"
				+ "(assert"
				+ "(let ((?x118 (bvslt (_ bv0 32) |c::jaja::main::1::k@1!0&0#1|)))"
				+ "(let ((?x119 (not ?x118)))"
				+ "(let ((?x120 (= true ?x119)))"
				+ "?x120))))"
				+ "(check-sat)"
				+ "(pop 1)"
				, log);
		Parser0 p = new Parser0(s, log);
		p.parse();
		assertTrue(true);
	}
}