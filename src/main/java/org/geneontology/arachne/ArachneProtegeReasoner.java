package org.geneontology.arachne;

import org.apache.jena.query.QueryExecution;
import org.apache.jena.query.QueryExecutionFactory;
import org.apache.jena.query.QueryFactory;
import org.apache.jena.query.QuerySolution;
import org.apache.jena.rdf.model.Model;
import org.apache.jena.rdf.model.ModelFactory;
import org.geneontology.jena.OWLtoRules;
import org.geneontology.rules.engine.*;
import org.geneontology.rules.util.Bridge;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.model.parameters.Imports;
import org.semanticweb.owlapi.reasoner.Node;
import org.semanticweb.owlapi.reasoner.*;
import org.semanticweb.owlapi.reasoner.impl.NodeFactory;
import org.semanticweb.owlapi.reasoner.impl.OWLClassNodeSet;
import org.semanticweb.owlapi.reasoner.impl.OWLNamedIndividualNodeSet;
import org.semanticweb.owlapi.reasoner.structural.StructuralReasonerFactory;
import org.semanticweb.owlapi.util.Version;
import org.semanticweb.owlapi.vocab.OWLRDFVocabulary;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import scala.collection.GenSet;
import scala.collection.JavaConverters;

import java.util.*;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.stream.Collectors;

public class ArachneProtegeReasoner implements OWLReasoner {

    private final Logger logger = LoggerFactory.getLogger(this.getClass());

    private final OWLOntology ontology;
    private final BufferingMode bufferingMode;
    private final OWLReasonerConfiguration config;
    private final ReasonerProgressMonitor monitor;

    private AtomicBoolean pendingRuleChanges = new AtomicBoolean(true);
    private AtomicBoolean pendingDataChanges = new AtomicBoolean(true);
    private final List<OWLOntologyChange> pendingChanges = new ArrayList<>();
    private final Set<OWLAxiom> pendingAxiomAdditions = new HashSet<>();
    private final Set<OWLAxiom> pendingAxiomRemovals = new HashSet<>();

    private RuleEngine arachne = null;
    private final Model model = ModelFactory.createDefaultModel();

    private final OWLDataFactory factory = OWLManager.getOWLDataFactory();

    private OWLReasoner structuralReasoner = null;

    private OWLOntologyChangeListener changeListener = new OWLOntologyChangeListener() {

        @Override
        public void ontologiesChanged(List<? extends OWLOntologyChange> changes) throws OWLException {
            for (OWLOntologyChange change : changes) {
                if (change.isImportChange()) {
                    pendingRuleChanges.set(true);
                    pendingDataChanges.set(true);
                    pendingChanges.add(change);
                }
                if (change.isAxiomChange()) {
                    pendingChanges.add(change);
                    if (change.isAddAxiom()) {
                        pendingAxiomAdditions.add(change.getAxiom());
                    } else if (change.isRemoveAxiom()) {
                        pendingAxiomRemovals.add(change.getAxiom());
                    }
                    if (change.getAxiom().isOfType(AxiomType.TBoxAndRBoxAxiomTypes)) {
                        pendingRuleChanges.set(true);
                        pendingDataChanges.set(true);
                    } else if (change.getAxiom().isOfType(AxiomType.ABoxAxiomTypes)) {
                        pendingDataChanges.set(true);
                    }
                }
            }
            if (bufferingMode == BufferingMode.NON_BUFFERING) flush();
        }

    };

    public ArachneProtegeReasoner(OWLOntology ontology, BufferingMode bufferingMode, OWLReasonerConfiguration config) {
        this.ontology = ontology;
        this.bufferingMode = bufferingMode;
        this.config = config;
        if (config.getProgressMonitor() != null) {
            this.monitor = config.getProgressMonitor();
        } else {
            this.monitor = new NullReasonerProgressMonitor();
        }
        ontology.getOWLOntologyManager().addOntologyChangeListener(changeListener);
        flush();
    }

    @Override
    public void dispose() {
        ontology.getOWLOntologyManager().removeOntologyChangeListener(changeListener);
    }

    @Override
    public void flush() {
        if (structuralReasoner == null) {
            monitor.reasonerTaskStarted("Creating structural reasoner for Tbox");
            monitor.reasonerTaskBusy();
            this.structuralReasoner = new StructuralReasonerFactory().createReasoner(ontology);
            this.structuralReasoner.flush();
            monitor.reasonerTaskStopped();
        } else {
            monitor.reasonerTaskStarted("Flushing structural reasoner");
            monitor.reasonerTaskBusy();
            this.structuralReasoner.flush();
            monitor.reasonerTaskStopped();
        }
        pendingAxiomAdditions.clear();
        pendingAxiomRemovals.clear();
        pendingChanges.clear();
        if (pendingRuleChanges.getAndSet(false)) {
            monitor.reasonerTaskStarted("Converting Tbox to rules");
            monitor.reasonerTaskBusy();
            scala.collection.Iterable<Rule> rules = Bridge.rulesFromJena(
                    ((GenSet<org.apache.jena.reasoner.rulesys.Rule>) (OWLtoRules.translate(ontology, Imports.INCLUDED, true, true, false, true)))
                            .union(OWLtoRules.indirectRules(ontology)).seq());
            monitor.reasonerTaskStopped();
            monitor.reasonerTaskStarted("Constructing rule engine from rules");
            monitor.reasonerTaskBusy();
            arachne = new RuleEngine(rules, true);
            monitor.reasonerTaskStopped();
        }
        if (pendingDataChanges.getAndSet(false)) {
            monitor.reasonerTaskStarted("Realizing Abox");
            monitor.reasonerTaskBusy();
            model.removeAll();
            Set<Triple> triples = ontology.getAxioms(AxiomType.OBJECT_PROPERTY_ASSERTION).stream().map(axiom -> asTriple(axiom)).collect(Collectors.toSet());
            triples.addAll(ontology.getAxioms(AxiomType.CLASS_ASSERTION).stream().flatMap(axiom -> asTriple(axiom).stream()).collect(Collectors.toSet()));
            WorkingMemory wm = arachne.processTriples(JavaConverters.asScalaSet(triples));
            for (Triple triple : JavaConverters.setAsJavaSet(wm.facts())) {
                model.add(model.asStatement(Bridge.jenaFromTriple(triple)));
            }
            monitor.reasonerTaskStopped();
        }
    }

    @Override
    public Node<OWLClass> getBottomClassNode() {
        return structuralReasoner.getBottomClassNode();
    }

    @Override
    public Node<OWLDataProperty> getBottomDataPropertyNode() {
        return structuralReasoner.getBottomDataPropertyNode();
    }

    @Override
    public Node<OWLObjectPropertyExpression> getBottomObjectPropertyNode() {
        return structuralReasoner.getBottomObjectPropertyNode();
    }

    @Override
    public BufferingMode getBufferingMode() {
        return this.bufferingMode;
    }

    @Override
    public NodeSet<OWLClass> getDataPropertyDomains(OWLDataProperty arg0, boolean arg1) {
        return structuralReasoner.getDataPropertyDomains(arg0, arg1);
    }

    @Override
    public Set<OWLLiteral> getDataPropertyValues(OWLNamedIndividual arg0, OWLDataProperty arg1) {
        return structuralReasoner.getDataPropertyValues(arg0, arg1);
    }

    @Override
    public NodeSet<OWLNamedIndividual> getDifferentIndividuals(OWLNamedIndividual ind) {
        String query = "PREFIX owl: <http://www.w3.org/2002/07/owl#> " +
                "SELECT DISTINCT ?o WHERE { " +
                "<" + ind.getIRI() + "> owl:differentFrom ?o . " +
                "FILTER(isIRI(?o))" +
                "}";
        return new OWLNamedIndividualNodeSet(
                executeSelect(query).stream().map(
                        qs -> NodeFactory.getOWLNamedIndividualNode(factory.getOWLNamedIndividual(IRI.create(qs.getResource("o").getURI()))))
                        .collect(Collectors.toSet()));
    }

    @Override
    public NodeSet<OWLClass> getDisjointClasses(OWLClassExpression arg0) {
        return structuralReasoner.getDisjointClasses(arg0);
    }

    @Override
    public NodeSet<OWLDataProperty> getDisjointDataProperties(OWLDataPropertyExpression arg0) {
        return structuralReasoner.getDisjointDataProperties(arg0);
    }

    @Override
    public NodeSet<OWLObjectPropertyExpression> getDisjointObjectProperties(OWLObjectPropertyExpression arg0) {
        return structuralReasoner.getDisjointObjectProperties(arg0);
    }

    @Override
    public Node<OWLClass> getEquivalentClasses(OWLClassExpression arg0) {
        return structuralReasoner.getEquivalentClasses(arg0);
    }

    @Override
    public Node<OWLDataProperty> getEquivalentDataProperties(OWLDataProperty arg0) {
        return structuralReasoner.getEquivalentDataProperties(arg0);
    }

    @Override
    public Node<OWLObjectPropertyExpression> getEquivalentObjectProperties(OWLObjectPropertyExpression arg0) {
        return structuralReasoner.getEquivalentObjectProperties(arg0);
    }

    @Override
    public FreshEntityPolicy getFreshEntityPolicy() {
        return config.getFreshEntityPolicy();
    }

    @Override
    public IndividualNodeSetPolicy getIndividualNodeSetPolicy() {
        return config.getIndividualNodeSetPolicy();
    }

    @Override
    public NodeSet<OWLNamedIndividual> getInstances(OWLClassExpression ce, boolean direct) {
        logger.info("Get instances: " + ce + " direct: " + direct);
        if (ce instanceof OWLObjectHasValue) {
            OWLObjectHasValue hasValue = (OWLObjectHasValue) ce;
            if (hasValue.getFiller() instanceof OWLNamedIndividual) {
                OWLNamedIndividual ind = (OWLNamedIndividual) (hasValue.getFiller());
                if (hasValue.getProperty() instanceof OWLObjectInverseOf) {
                    return getObjectPropertyValues(ind, ((OWLObjectInverseOf) hasValue.getProperty()).getInverse());
                } else {
                    return getObjectPropertyValues(ind, hasValue.getProperty().getInverseProperty());
                }
            } else throw new UnsupportedOperationException();
        } else if (ce.isAnonymous()) {
            throw new UnsupportedOperationException();
        } else {
            final String query;
            if (direct) {
                query = "PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> " +
                        "SELECT DISTINCT ?s WHERE { " +
                        "?s rdf:type <" + ce.asOWLClass().getIRI() + "> " +
                        "FILTER(isIRI(?s)) " +
                        "FILTER NOT EXISTS {?s <" + OWLtoRules.IndirectType() + "> <" + ce.asOWLClass().getIRI() + "> ." + "}" +
                        "}";
            } else {
                query = "PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> " +
                        "SELECT DISTINCT ?s WHERE { " +
                        "?s rdf:type <" + ce.asOWLClass().getIRI() + "> " +
                        "FILTER(isIRI(?s)) " +
                        "}";
            }
            return new OWLNamedIndividualNodeSet(
                    executeSelect(query).stream().map(
                            qs -> NodeFactory.getOWLNamedIndividualNode(factory.getOWLNamedIndividual(IRI.create(qs.getResource("s").getURI()))))
                            .collect(Collectors.toSet()));
        }
    }

    @Override
    public Node<OWLObjectPropertyExpression> getInverseObjectProperties(OWLObjectPropertyExpression arg0) {
        return structuralReasoner.getInverseObjectProperties(arg0);
    }

    @Override
    public NodeSet<OWLClass> getObjectPropertyDomains(OWLObjectPropertyExpression arg0, boolean arg1) {
        return structuralReasoner.getObjectPropertyDomains(arg0, arg1);
    }

    @Override
    public NodeSet<OWLClass> getObjectPropertyRanges(OWLObjectPropertyExpression arg0, boolean arg1) {
        return structuralReasoner.getObjectPropertyRanges(arg0, arg1);
    }

    @Override
    public NodeSet<OWLNamedIndividual> getObjectPropertyValues(OWLNamedIndividual ind, OWLObjectPropertyExpression pe) {
        final String predicate;
        if (pe instanceof OWLObjectInverseOf) {
            predicate = "^<" + pe.getInverseProperty().asOWLObjectProperty().getIRI() + ">";
        } else {
            predicate = "<" + pe.asOWLObjectProperty().getIRI() + ">";
        }
        String query = "SELECT DISTINCT ?o WHERE { " +
                "<" + ind.getIRI() + "> " + predicate + " ?o ." +
                "FILTER(isIRI(?o)) " +
                "}";
        return new OWLNamedIndividualNodeSet(
                executeSelect(query).stream().map(
                        qs -> NodeFactory.getOWLNamedIndividualNode(factory.getOWLNamedIndividual(IRI.create(qs.getResource("o").getURI()))))
                        .collect(Collectors.toSet()));
    }

    @Override
    public Set<OWLAxiom> getPendingAxiomAdditions() {
        return this.pendingAxiomAdditions;
    }

    @Override
    public Set<OWLAxiom> getPendingAxiomRemovals() {
        return this.pendingAxiomRemovals;
    }

    @Override
    public List<OWLOntologyChange> getPendingChanges() {
        return this.pendingChanges;
    }

    @Override
    public Set<InferenceType> getPrecomputableInferenceTypes() {
        return Collections.emptySet();
    }

    @Override
    public String getReasonerName() {
        return "Arachne";
    }

    @Override
    public Version getReasonerVersion() {
        return new Version(0, 0, 0, 0); //FIXME
    }

    @Override
    public OWLOntology getRootOntology() {
        return this.ontology;
    }

    @Override
    public Node<OWLNamedIndividual> getSameIndividuals(OWLNamedIndividual ind) {
        String query = "PREFIX owl: <http://www.w3.org/2002/07/owl#> " +
                "SELECT DISTINCT ?o WHERE { " +
                "<" + ind.getIRI() + "> owl:sameAs ?o . " +
                "FILTER(isIRI(?o)) " +
                "}";
        return NodeFactory.getOWLNamedIndividualNode(
                executeSelect(query).stream().map(
                        qs -> factory.getOWLNamedIndividual(IRI.create(qs.getResource("o").getURI())))
                        .collect(Collectors.toSet()));
    }

    @Override
    public NodeSet<OWLClass> getSubClasses(OWLClassExpression arg0, boolean arg1) {
        return structuralReasoner.getSubClasses(arg0, arg1);
    }

    @Override
    public NodeSet<OWLDataProperty> getSubDataProperties(OWLDataProperty arg0, boolean arg1) {
        return structuralReasoner.getSubDataProperties(arg0, arg1);
    }

    @Override
    public NodeSet<OWLObjectPropertyExpression> getSubObjectProperties(OWLObjectPropertyExpression arg0, boolean arg1) {
        return structuralReasoner.getSubObjectProperties(arg0, arg1);
    }

    @Override
    public NodeSet<OWLClass> getSuperClasses(OWLClassExpression arg0, boolean arg1) {
        return structuralReasoner.getSuperClasses(arg0, arg1);
    }

    @Override
    public NodeSet<OWLDataProperty> getSuperDataProperties(OWLDataProperty arg0, boolean arg1) {
        return structuralReasoner.getSuperDataProperties(arg0, arg1);
    }

    @Override
    public NodeSet<OWLObjectPropertyExpression> getSuperObjectProperties(OWLObjectPropertyExpression arg0, boolean arg1) {
        return structuralReasoner.getSuperObjectProperties(arg0, arg1);
    }

    @Override
    public long getTimeOut() {
        return Long.MAX_VALUE;
    }

    @Override
    public Node<OWLClass> getTopClassNode() {
        return structuralReasoner.getTopClassNode();
    }

    @Override
    public Node<OWLDataProperty> getTopDataPropertyNode() {
        return structuralReasoner.getTopDataPropertyNode();
    }

    @Override
    public Node<OWLObjectPropertyExpression> getTopObjectPropertyNode() {
        return structuralReasoner.getTopObjectPropertyNode();
    }

    @Override
    public NodeSet<OWLClass> getTypes(OWLNamedIndividual ind, boolean direct) {
        final String query;
        if (direct) {
            query = "PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> " +
                    "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#> " +
                    "PREFIX owl: <http://www.w3.org/2002/07/owl#> " +
                    "SELECT DISTINCT ?o WHERE { " +
                    "<" + ind.getIRI() + "> rdf:type ?o . " +
                    "FILTER(isIRI(?o)) " +
                    "FILTER(?o != owl:NamedIndividual) " +
                    "FILTER NOT EXISTS { <" + ind.getIRI() + "> <" + OWLtoRules.IndirectType() + "> ?o . } " +
                    "}";

        } else {
            query = "PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> " +
                    "PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#> " +
                    "PREFIX owl: <http://www.w3.org/2002/07/owl#> " +
                    "SELECT DISTINCT ?o WHERE { " +
                    "<" + ind.getIRI() + "> rdf:type ?o . " +
                    "FILTER(isIRI(?o)) " +
                    "FILTER(?o != owl:NamedIndividual) " +
                    "}";
        }
        return new OWLClassNodeSet(
                executeSelect(query).stream().map(
                        qs -> NodeFactory.getOWLClassNode(factory.getOWLClass(IRI.create(qs.getResource("o").getURI()))))
                        .collect(Collectors.toSet()));
    }

    @Override
    public Node<OWLClass> getUnsatisfiableClasses() {
        return structuralReasoner.getUnsatisfiableClasses();
    }

    @Override
    public void interrupt() {
        //FIXME
    }

    @Override
    public boolean isConsistent() {
        String query = "PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> " +
                "PREFIX owl: <http://www.w3.org/2002/07/owl#> " +
                "ASK WHERE { " +
                "?s rdf:type owl:Nothing . " +
                "}";
        return !executeAsk(query);
    }

    @Override
    public boolean isEntailed(OWLAxiom axiom) {
        logger.info("Is entailed? " + axiom);
        if (axiom instanceof OWLClassAssertionAxiom) {
            return asTriple(((OWLClassAssertionAxiom) axiom)).stream().map(t -> model.asStatement(Bridge.jenaFromTriple(t))).allMatch(s -> model.contains(s));
        } else if (axiom instanceof OWLObjectPropertyAssertionAxiom) {
            return model.contains(model.asStatement(Bridge.jenaFromTriple(asTriple((OWLObjectPropertyAssertionAxiom) axiom))));
        } else return structuralReasoner.isEntailed(axiom);
    }

    @Override
    public boolean isEntailed(Set<? extends OWLAxiom> axioms) {
        return axioms.stream().allMatch(ax -> isEntailed(ax));
    }

    @Override
    public boolean isEntailmentCheckingSupported(AxiomType<?> axiomType) {
        return AxiomType.ABoxAxiomTypes.contains(axiomType);
    }

    @Override
    public boolean isPrecomputed(InferenceType arg0) {
        return false;
    }

    @Override
    public boolean isSatisfiable(OWLClassExpression cls) {
        logger.info("Is satisfiable? " + cls);
        // First we handle the special case that a class assertion or object property assertion is being checked by the OWL API explanation tool.
        // We need to include inferences made by the rule engine.
        if (cls instanceof OWLObjectIntersectionOf) {
            OWLObjectIntersectionOf intersection = (OWLObjectIntersectionOf) cls;
            if (intersection.getOperands().size() == 2) {
                List<OWLClassExpression> operands = intersection.getOperandsAsList();
                OWLClassExpression first = operands.get(0);
                OWLClassExpression second = operands.get(1);
                final OWLObjectOneOf oneOf;
                final OWLObjectComplementOf not;
                if (first instanceof OWLObjectOneOf && second instanceof OWLObjectComplementOf) {
                    oneOf = (OWLObjectOneOf) first;
                    not = (OWLObjectComplementOf) second;
                } else if (first instanceof OWLObjectComplementOf && second instanceof OWLObjectOneOf) {
                    oneOf = (OWLObjectOneOf) second;
                    not = (OWLObjectComplementOf) first;
                } else {
                    oneOf = null;
                    not = null;
                }
                if (oneOf != null && not != null && oneOf.getIndividuals().size() == 1) {
                    OWLIndividual individual = oneOf.getIndividuals().iterator().next();
                    if (individual instanceof OWLNamedIndividual) {
                        OWLNamedIndividual named = (OWLNamedIndividual) individual;
                        return !(getInstances(not.getOperand(), false).getFlattened().contains(named));
                    }
                }
            }
        }
        return structuralReasoner.isSatisfiable(cls);
    }

    @Override
    public void precomputeInferences(InferenceType... arg0) {
    }

    private List<QuerySolution> executeSelect(String query) {
        List<QuerySolution> solutions = new ArrayList<>();
        QueryExecution execution = QueryExecutionFactory.create(QueryFactory.create(query), model);
        execution.execSelect().forEachRemaining(qs -> solutions.add(qs));
        execution.close();
        return solutions;
    }

    private Model executeConstruct(String query) {
        QueryExecution execution = QueryExecutionFactory.create(QueryFactory.create(query), model);
        Model model = execution.execConstruct();
        execution.close();
        return model;
    }

    private boolean executeAsk(String query) {
        QueryExecution execution = QueryExecutionFactory.create(QueryFactory.create(query), model);
        boolean result = execution.execAsk();
        execution.close();
        return result;
    }

    private Triple asTriple(OWLObjectPropertyAssertionAxiom axiom) {
        final Resource subject;
        if (axiom.getSubject().isNamed()) {
            subject = new URI(axiom.getSubject().asOWLNamedIndividual().getIRI().toString());
        } else {
            subject = new BlankNode(axiom.getSubject().asOWLAnonymousIndividual().getID().getID());
        }
        final URI property;
        final boolean inverse;
        if (axiom.getProperty().isAnonymous()) {
            property = new URI(axiom.getProperty().getInverseProperty().asOWLObjectProperty().getIRI().toString());
            inverse = true;
        } else {
            property = new URI(axiom.getProperty().asOWLObjectProperty().getIRI().toString());
            inverse = false;
        }
        final Resource object;
        if (axiom.getObject().isNamed()) {
            object = new URI(axiom.getObject().asOWLNamedIndividual().getIRI().toString());
        } else {
            object = new BlankNode(axiom.getObject().asOWLAnonymousIndividual().getID().getID());
        }
        if (inverse) return new Triple(object, property, subject);
        else return new Triple(subject, property, object);
    }

    private Set<Triple> asTriple(OWLClassAssertionAxiom axiom) {
        final Resource subject;
        if (axiom.getIndividual().isNamed()) {
            subject = new URI(axiom.getIndividual().asOWLNamedIndividual().getIRI().toString());
        } else {
            subject = new BlankNode(axiom.getIndividual().asOWLAnonymousIndividual().getID().getID());
        }
        if (axiom.getClassExpression().isAnonymous()) {
            return Collections.emptySet();
        } else {
            URI cls = new URI(axiom.getClassExpression().asOWLClass().getIRI().toString());
            URI rdfType = new URI(OWLRDFVocabulary.RDF_TYPE.getIRI().toString());
            return Collections.singleton(new Triple(subject, rdfType, cls));
        }
    }

}
