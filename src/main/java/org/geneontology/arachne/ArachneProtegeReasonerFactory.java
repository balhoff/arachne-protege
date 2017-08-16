package org.geneontology.arachne;

import org.apache.jena.system.JenaSystem;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.reasoner.BufferingMode;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.OWLReasonerConfiguration;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;
import org.semanticweb.owlapi.reasoner.SimpleConfiguration;

public class ArachneProtegeReasonerFactory implements OWLReasonerFactory {

	public ArachneProtegeReasonerFactory() {
		JenaSystem.init();
	}

	@Override
	public OWLReasoner createNonBufferingReasoner(OWLOntology ontology) {
		return new ArachneProtegeReasoner(ontology, BufferingMode.NON_BUFFERING, new SimpleConfiguration());
	}

	@Override
	public OWLReasoner createNonBufferingReasoner(OWLOntology ontology, OWLReasonerConfiguration config) {
		return new ArachneProtegeReasoner(ontology, BufferingMode.NON_BUFFERING, config);
	}

	@Override
	public OWLReasoner createReasoner(OWLOntology ontology) {
		return new ArachneProtegeReasoner(ontology, BufferingMode.BUFFERING, new SimpleConfiguration());
	}

	@Override
	public OWLReasoner createReasoner(OWLOntology ontology, OWLReasonerConfiguration config) {
		return new ArachneProtegeReasoner(ontology, BufferingMode.BUFFERING, config);
	}

	@Override
	public String getReasonerName() {
		return "Arachne";
	}

}
