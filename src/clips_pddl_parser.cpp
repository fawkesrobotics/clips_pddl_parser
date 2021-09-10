
/***************************************************************************
 *  clips_pddl_parser.cpp - Parse PDDL files to a CLIPS environment
 *
 *  Created: Tue Apr 16 13:51:14 2013
 *  Copyright  2013  Tim Niemueller [www.niemueller.de]
 *             2021  Till Hofmann <hofmann@kbsg.rwth-aachen.de>
 ****************************************************************************/

/*  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 * - Redistributions of source code must retain the above copyright
 *   notice, this list of conditions and the following disclaimer.
 * - Redistributions in binary form must reproduce the above copyright
 *   notice, this list of conditions and the following disclaimer in
 *   the documentation and/or other materials provided with the
 *   distribution.
 * - Neither the name of the authors nor the names of its contributors
 *   may be used to endorse or promote products derived from this
 *   software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include <clips_pddl_parser/clips_pddl_parser.h>
#include <clips_pddl_parser/effect_visitor.h>
#include <clips_pddl_parser/precondition_visitor.h>
#include <pddl_parser/pddl_parser.h>
#include <spdlog/spdlog.h>

#include <clipsmm.h>
#include <filesystem>
#include <fstream>

using namespace std;
using namespace pddl_parser;

namespace {
#ifdef SHAREDIR
const std::filesystem::path sharedir(SHAREDIR);
#else
const std::filesystem::path sharedir{"clips"};
#endif
} // namespace

namespace clips_pddl_parser {

/** @class ClipsPddlParser <clips_pddl_parser/communicator.h>
 * PDDL parser CLIPS integration class.
 * This class provides functionality to parse a PDDL domain to a given CLIPS
 * environment. It stores the relevant domain information to dedicated facts.
 */

/** Constructor.
 * @param env CLIPS environment to which to provide the PDDL parsing
 * functionality
 * @param env_mutex mutex to lock when operating on the CLIPS environment.
 * @param load_clips_templates If true, the target CLIPS fact templates are
 *                             loaded to the environment.
 */
ClipsPddlParser::ClipsPddlParser(CLIPS::Environment *env,
                                 std::mutex &        env_mutex,
                                 bool                load_clips_templates)
: clips_(env), clips_mutex_(env_mutex)
{
	setup_clips(load_clips_templates);
}

/** Destructor. */
ClipsPddlParser::~ClipsPddlParser()
{
	{
		std::lock_guard<std::mutex> lock(clips_mutex_);

		for (auto f : functions_) {
			clips_->remove_function(f);
		}
		functions_.clear();
	}
}

#define ADD_FUNCTION(n, s)    \
	clips_->add_function(n, s); \
	functions_.push_back(n);

/** Setup CLIPS environment.
 * @param load_clips_templates If true, the target CLIPS fact templates are
 *                             loaded to the environment.
 */
void
ClipsPddlParser::setup_clips(bool load_clips_templates)
{
	std::lock_guard<std::mutex> lock(clips_mutex_);
	ADD_FUNCTION("parse-pddl-domain",
	             (sigc::slot<void, string>(sigc::mem_fun(*this, &ClipsPddlParser::parse_domain))));
	if (load_clips_templates) {
		clips_->batch_evaluate((sharedir / "domain.clp").string());
	}
}
/** CLIPS function to parse a PDDL domain.
 * This parses the given domain and asserts domain facts for all parts of the
 * domain.
 * @param domain_file The path of the domain file to parse.
 */
void
ClipsPddlParser::parse_domain(std::string domain_file)
{
	Domain domain;
	try {
		ifstream     df(domain_file);
		stringstream buffer;
		buffer << df.rdbuf();
		domain = PddlParser::parseDomain(buffer.str());
	} catch (PddlParserException &e) {
		SPDLOG_WARN(std::string("CLIPS_PDDL_Parser: Failed to parse domain:") + e.what());
		return;
	}
	std::lock_guard<std::mutex> lock(clips_mutex_);

	for (const auto &temp : {"pddl-formula",
	                         "pddl-predicate",
	                         "domain-effect",
	                         "domain-object-type",
	                         "domain-predicate",
	                         "domain-operator-parameter",
	                         "domain-operator"}) {
		CLIPS::Template::pointer domain_op = clips_->get_template("domain-operator");
		if (!clips_->get_template(temp)) {
			SPDLOG_WARN(std::string("CLIPS_PDDL_Parser: Did not get template ") + temp
			            + ", did you load pddl_domain.clp?");
		}
	}

	CLIPS::Template::pointer clips_template = clips_->get_template("domain-object-type");
	for (auto &type : domain.types) {
		CLIPS::Fact::pointer fact = CLIPS::Fact::create(*clips_, clips_template);
		fact->set_slot("name", type.first);

		if (!type.second.empty()) {
			fact->set_slot("super-type", type.second);
		}

		CLIPS::Fact::pointer new_fact = clips_->assert_fact(fact);
		if (!new_fact) {
			SPDLOG_WARN("CLIPS_PDDL_Parser: Asserting domain-object-type fact failed");
		}
	}

	clips_template = clips_->get_template("domain-predicate");
	for (auto &predicate : domain.predicates) {
		string param_string = "";
		string type_string  = "";
		for (auto &param : predicate.second) {
			param_string += " " + param.first;
			type_string += " " + param.second;
		}
		CLIPS::Fact::pointer fact = CLIPS::Fact::create(*clips_, clips_template);
		fact->set_slot("name", predicate.first);
		fact->set_slot("param-names", param_string);
		fact->set_slot("param-types", type_string);
		CLIPS::Fact::pointer new_fact = clips_->assert_fact(fact);
		if (!new_fact) {
			SPDLOG_WARN("CLIPS_PDDL_Parser: Asserting domain-predicate fact failed");
		}
	}

	clips_template = clips_->get_template("domain-operator-parameter");
	for (auto &action : domain.actions) {
		string params_string = "";
		for (auto &param_pair : action.action_params) {
			string param_name = param_pair.first;
			string param_type = param_pair.second;
			params_string += " " + param_name;
			CLIPS::Fact::pointer fact = CLIPS::Fact::create(*clips_, clips_template);
			fact->set_slot("name", param_name);
			fact->set_slot("operator", action.name);
			fact->set_slot("type", param_type);
			CLIPS::Fact::pointer new_fact = clips_->assert_fact(fact);

			if (!new_fact) {
				SPDLOG_WARN("CLIPS_PDDL_Parser: Asserting domain-operator-parameter "
				            "fact failed");
			}
		}
		clips_template            = clips_->get_template("domain-operator");
		CLIPS::Fact::pointer fact = CLIPS::Fact::create(*clips_, clips_template);
		fact->set_slot("name", action.name);
		fact->set_slot("param-names", params_string);
		CLIPS::Fact::pointer new_fact = clips_->assert_fact(fact);
		if (!new_fact) {
			SPDLOG_WARN("CLIPS_PDDL_Parser: Asserting domain-operator fact failed");
		}

		vector<string> precondition_facts =
		  boost::apply_visitor(PreconditionToCLIPSFactVisitor(action.name, 1, true),
		                       action.precondition.expression);
		for (auto &fact : precondition_facts) {
			clips_->assert_fact(fact);
		}
		vector<string> effect_facts =
		  boost::apply_visitor(EffectToCLIPSFactVisitor(action.name, true), action.effect.expression);
		for (auto &fact : effect_facts) {
			clips_->assert_fact(fact);
		}
	}
}

} // end namespace clips_pddl_parser
