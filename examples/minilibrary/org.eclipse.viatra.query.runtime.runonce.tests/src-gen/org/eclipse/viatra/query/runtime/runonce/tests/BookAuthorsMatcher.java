package org.eclipse.viatra.query.runtime.runonce.tests;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import org.apache.log4j.Logger;
import org.eclipse.emf.common.notify.Notifier;
import org.eclipse.viatra.examples.library.Book;
import org.eclipse.viatra.examples.library.Writer;
import org.eclipse.viatra.query.runtime.api.IMatchProcessor;
import org.eclipse.viatra.query.runtime.api.IQuerySpecification;
import org.eclipse.viatra.query.runtime.api.ViatraQueryEngine;
import org.eclipse.viatra.query.runtime.api.impl.BaseMatcher;
import org.eclipse.viatra.query.runtime.exception.ViatraQueryException;
import org.eclipse.viatra.query.runtime.matchers.tuple.Tuple;
import org.eclipse.viatra.query.runtime.runonce.tests.BookAuthorsMatch;
import org.eclipse.viatra.query.runtime.runonce.tests.util.BookAuthorsQuerySpecification;
import org.eclipse.viatra.query.runtime.util.ViatraQueryLoggingUtil;

/**
 * Generated pattern matcher API of the org.eclipse.viatra.query.runtime.runonce.tests.bookAuthors pattern,
 * providing pattern-specific query methods.
 * 
 * <p>Use the pattern matcher on a given model via {@link #on(ViatraQueryEngine)},
 * e.g. in conjunction with {@link ViatraQueryEngine#on(Notifier)}.
 * 
 * <p>Matches of the pattern will be represented as {@link BookAuthorsMatch}.
 * 
 * <p>Original source:
 * <code><pre>
 * pattern bookAuthors(book : Book, author) {
 * 	Book.authors(book, author);
 * }
 * </pre></code>
 * 
 * @see BookAuthorsMatch
 * @see BookAuthorsProcessor
 * @see BookAuthorsQuerySpecification
 * 
 */
@SuppressWarnings("all")
public class BookAuthorsMatcher extends BaseMatcher<BookAuthorsMatch> {
  /**
   * Initializes the pattern matcher within an existing VIATRA Query engine.
   * If the pattern matcher is already constructed in the engine, only a light-weight reference is returned.
   * The match set will be incrementally refreshed upon updates.
   * @param engine the existing VIATRA Query engine in which this matcher will be created.
   * @throws ViatraQueryException if an error occurs during pattern matcher creation
   * 
   */
  public static BookAuthorsMatcher on(final ViatraQueryEngine engine) throws ViatraQueryException {
    // check if matcher already exists
    BookAuthorsMatcher matcher = engine.getExistingMatcher(querySpecification());
    if (matcher == null) {
    	matcher = new BookAuthorsMatcher(engine);
    	// do not have to "put" it into engine.matchers, reportMatcherInitialized() will take care of it
    }
    return matcher;
  }
  
  private final static int POSITION_BOOK = 0;
  
  private final static int POSITION_AUTHOR = 1;
  
  private final static Logger LOGGER = ViatraQueryLoggingUtil.getLogger(BookAuthorsMatcher.class);
  
  /**
   * Initializes the pattern matcher over a given EMF model root (recommended: Resource or ResourceSet).
   * If a pattern matcher is already constructed with the same root, only a light-weight reference is returned.
   * The scope of pattern matching will be the given EMF model root and below (see FAQ for more precise definition).
   * The match set will be incrementally refreshed upon updates from this scope.
   * <p>The matcher will be created within the managed {@link ViatraQueryEngine} belonging to the EMF model root, so
   * multiple matchers will reuse the same engine and benefit from increased performance and reduced memory footprint.
   * @param emfRoot the root of the EMF containment hierarchy where the pattern matcher will operate. Recommended: Resource or ResourceSet.
   * @throws ViatraQueryException if an error occurs during pattern matcher creation
   * @deprecated use {@link #on(ViatraQueryEngine)} instead, e.g. in conjunction with {@link ViatraQueryEngine#on(Notifier)}
   * 
   */
  @Deprecated
  public BookAuthorsMatcher(final Notifier emfRoot) throws ViatraQueryException {
    this(ViatraQueryEngine.on(emfRoot));
  }
  
  /**
   * Initializes the pattern matcher within an existing VIATRA Query engine.
   * If the pattern matcher is already constructed in the engine, only a light-weight reference is returned.
   * The match set will be incrementally refreshed upon updates.
   * @param engine the existing VIATRA Query engine in which this matcher will be created.
   * @throws ViatraQueryException if an error occurs during pattern matcher creation
   * @deprecated use {@link #on(ViatraQueryEngine)} instead
   * 
   */
  @Deprecated
  public BookAuthorsMatcher(final ViatraQueryEngine engine) throws ViatraQueryException {
    super(engine, querySpecification());
  }
  
  /**
   * Returns the set of all matches of the pattern that conform to the given fixed values of some parameters.
   * @param pBook the fixed value of pattern parameter book, or null if not bound.
   * @param pAuthor the fixed value of pattern parameter author, or null if not bound.
   * @return matches represented as a BookAuthorsMatch object.
   * 
   */
  public Collection<BookAuthorsMatch> getAllMatches(final Book pBook, final Writer pAuthor) {
    return rawGetAllMatches(new Object[]{pBook, pAuthor});
  }
  
  /**
   * Returns an arbitrarily chosen match of the pattern that conforms to the given fixed values of some parameters.
   * Neither determinism nor randomness of selection is guaranteed.
   * @param pBook the fixed value of pattern parameter book, or null if not bound.
   * @param pAuthor the fixed value of pattern parameter author, or null if not bound.
   * @return a match represented as a BookAuthorsMatch object, or null if no match is found.
   * 
   */
  public BookAuthorsMatch getOneArbitraryMatch(final Book pBook, final Writer pAuthor) {
    return rawGetOneArbitraryMatch(new Object[]{pBook, pAuthor});
  }
  
  /**
   * Indicates whether the given combination of specified pattern parameters constitute a valid pattern match,
   * under any possible substitution of the unspecified parameters (if any).
   * @param pBook the fixed value of pattern parameter book, or null if not bound.
   * @param pAuthor the fixed value of pattern parameter author, or null if not bound.
   * @return true if the input is a valid (partial) match of the pattern.
   * 
   */
  public boolean hasMatch(final Book pBook, final Writer pAuthor) {
    return rawHasMatch(new Object[]{pBook, pAuthor});
  }
  
  /**
   * Returns the number of all matches of the pattern that conform to the given fixed values of some parameters.
   * @param pBook the fixed value of pattern parameter book, or null if not bound.
   * @param pAuthor the fixed value of pattern parameter author, or null if not bound.
   * @return the number of pattern matches found.
   * 
   */
  public int countMatches(final Book pBook, final Writer pAuthor) {
    return rawCountMatches(new Object[]{pBook, pAuthor});
  }
  
  /**
   * Executes the given processor on each match of the pattern that conforms to the given fixed values of some parameters.
   * @param pBook the fixed value of pattern parameter book, or null if not bound.
   * @param pAuthor the fixed value of pattern parameter author, or null if not bound.
   * @param processor the action that will process each pattern match.
   * 
   */
  public void forEachMatch(final Book pBook, final Writer pAuthor, final IMatchProcessor<? super BookAuthorsMatch> processor) {
    rawForEachMatch(new Object[]{pBook, pAuthor}, processor);
  }
  
  /**
   * Executes the given processor on an arbitrarily chosen match of the pattern that conforms to the given fixed values of some parameters.
   * Neither determinism nor randomness of selection is guaranteed.
   * @param pBook the fixed value of pattern parameter book, or null if not bound.
   * @param pAuthor the fixed value of pattern parameter author, or null if not bound.
   * @param processor the action that will process the selected match.
   * @return true if the pattern has at least one match with the given parameter values, false if the processor was not invoked
   * 
   */
  public boolean forOneArbitraryMatch(final Book pBook, final Writer pAuthor, final IMatchProcessor<? super BookAuthorsMatch> processor) {
    return rawForOneArbitraryMatch(new Object[]{pBook, pAuthor}, processor);
  }
  
  /**
   * Returns a new (partial) match.
   * This can be used e.g. to call the matcher with a partial match.
   * <p>The returned match will be immutable. Use {@link #newEmptyMatch()} to obtain a mutable match object.
   * @param pBook the fixed value of pattern parameter book, or null if not bound.
   * @param pAuthor the fixed value of pattern parameter author, or null if not bound.
   * @return the (partial) match object.
   * 
   */
  public BookAuthorsMatch newMatch(final Book pBook, final Writer pAuthor) {
    return BookAuthorsMatch.newMatch(pBook, pAuthor);
  }
  
  /**
   * Retrieve the set of values that occur in matches for book.
   * @return the Set of all values, null if no parameter with the given name exists, empty set if there are no matches
   * 
   */
  protected Set<Book> rawAccumulateAllValuesOfbook(final Object[] parameters) {
    Set<Book> results = new HashSet<Book>();
    rawAccumulateAllValues(POSITION_BOOK, parameters, results);
    return results;
  }
  
  /**
   * Retrieve the set of values that occur in matches for book.
   * @return the Set of all values, null if no parameter with the given name exists, empty set if there are no matches
   * 
   */
  public Set<Book> getAllValuesOfbook() {
    return rawAccumulateAllValuesOfbook(emptyArray());
  }
  
  /**
   * Retrieve the set of values that occur in matches for book.
   * @return the Set of all values, null if no parameter with the given name exists, empty set if there are no matches
   * 
   */
  public Set<Book> getAllValuesOfbook(final BookAuthorsMatch partialMatch) {
    return rawAccumulateAllValuesOfbook(partialMatch.toArray());
  }
  
  /**
   * Retrieve the set of values that occur in matches for book.
   * @return the Set of all values, null if no parameter with the given name exists, empty set if there are no matches
   * 
   */
  public Set<Book> getAllValuesOfbook(final Writer pAuthor) {
    return rawAccumulateAllValuesOfbook(new Object[]{
    null, 
    pAuthor
    });
  }
  
  /**
   * Retrieve the set of values that occur in matches for author.
   * @return the Set of all values, null if no parameter with the given name exists, empty set if there are no matches
   * 
   */
  protected Set<Writer> rawAccumulateAllValuesOfauthor(final Object[] parameters) {
    Set<Writer> results = new HashSet<Writer>();
    rawAccumulateAllValues(POSITION_AUTHOR, parameters, results);
    return results;
  }
  
  /**
   * Retrieve the set of values that occur in matches for author.
   * @return the Set of all values, null if no parameter with the given name exists, empty set if there are no matches
   * 
   */
  public Set<Writer> getAllValuesOfauthor() {
    return rawAccumulateAllValuesOfauthor(emptyArray());
  }
  
  /**
   * Retrieve the set of values that occur in matches for author.
   * @return the Set of all values, null if no parameter with the given name exists, empty set if there are no matches
   * 
   */
  public Set<Writer> getAllValuesOfauthor(final BookAuthorsMatch partialMatch) {
    return rawAccumulateAllValuesOfauthor(partialMatch.toArray());
  }
  
  /**
   * Retrieve the set of values that occur in matches for author.
   * @return the Set of all values, null if no parameter with the given name exists, empty set if there are no matches
   * 
   */
  public Set<Writer> getAllValuesOfauthor(final Book pBook) {
    return rawAccumulateAllValuesOfauthor(new Object[]{
    pBook, 
    null
    });
  }
  
  @Override
  protected BookAuthorsMatch tupleToMatch(final Tuple t) {
    try {
    	return BookAuthorsMatch.newMatch((Book) t.get(POSITION_BOOK), (Writer) t.get(POSITION_AUTHOR));
    } catch(ClassCastException e) {
    	LOGGER.error("Element(s) in tuple not properly typed!",e);
    	return null;
    }
  }
  
  @Override
  protected BookAuthorsMatch arrayToMatch(final Object[] match) {
    try {
    	return BookAuthorsMatch.newMatch((Book) match[POSITION_BOOK], (Writer) match[POSITION_AUTHOR]);
    } catch(ClassCastException e) {
    	LOGGER.error("Element(s) in array not properly typed!",e);
    	return null;
    }
  }
  
  @Override
  protected BookAuthorsMatch arrayToMatchMutable(final Object[] match) {
    try {
    	return BookAuthorsMatch.newMutableMatch((Book) match[POSITION_BOOK], (Writer) match[POSITION_AUTHOR]);
    } catch(ClassCastException e) {
    	LOGGER.error("Element(s) in array not properly typed!",e);
    	return null;
    }
  }
  
  /**
   * @return the singleton instance of the query specification of this pattern
   * @throws ViatraQueryException if the pattern definition could not be loaded
   * 
   */
  public static IQuerySpecification<BookAuthorsMatcher> querySpecification() throws ViatraQueryException {
    return BookAuthorsQuerySpecification.instance();
  }
}
