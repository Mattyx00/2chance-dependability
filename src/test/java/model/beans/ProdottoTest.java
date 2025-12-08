package model.beans;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;

import org.junit.jupiter.params.provider.NullAndEmptySource;
import org.junit.jupiter.params.provider.ValueSource;

import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.mock;

class ProdottoTest {

    private Prodotto product;

    @BeforeEach
    void setUp() {
        product = new Prodotto();
    }

    // --- Constructor ---

    @Test
    @DisplayName("F1: Default constructor initializes fields correctly")
    void testDefaultConstructor() {
        // Act & Assert
        assertNotNull(product);
        assertAll("Default values",
                () -> assertEquals(0, product.getId()),
                () -> assertEquals(0, product.getQuantitaProdotto()),
                () -> assertEquals(0.0, product.getPrezzo()),
                () -> assertEquals(0.0, product.getPeso()),
                () -> assertNull(product.getDimensioni()),
                () -> assertNull(product.getMarca()),
                () -> assertNull(product.getModello()),
                () -> assertNull(product.getImmagine()),
                () -> assertNull(product.getDescrizione()),
                () -> assertNull(product.getCategoria()),
                () -> assertNull(product.getRecensioni()),
                () -> assertNull(product.getSpecifiche()));
    }

    // --- setSpecifiche ---

    @Test
    @DisplayName("F1: setSpecifiche throws IllegalArgumentException when specifiche is null")
    void shouldThrowExceptionWhenSpecificheIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> product.setSpecifiche(null));
        assertEquals("La lista delle specifiche non può essere null", exception.getMessage());
    }

    @Test
    @DisplayName("F2: setSpecifiche sets the list when empty")
    void shouldSetSpecificheWhenEmpty() {
        // Arrange
        ArrayList<Specifiche> emptySpecsList = new ArrayList<>();

        // Act
        product.setSpecifiche(emptySpecsList);

        // Assert
        assertEquals(emptySpecsList, product.getSpecifiche());
    }

    @Test
    @DisplayName("F3: setSpecifiche sets the list when populated")
    void shouldSetSpecificheWhenPopulated() {
        // Arrange
        ArrayList<Specifiche> populatedSpecsList = new ArrayList<>();
        Specifiche mockSpecification = mock(Specifiche.class);
        populatedSpecsList.add(mockSpecification);

        // Act
        product.setSpecifiche(populatedSpecsList);

        // Assert
        assertEquals(populatedSpecsList, product.getSpecifiche());
    }

    // --- setRecensioni ---

    @Test
    @DisplayName("F1: setRecensioni throws IllegalArgumentException when recensioni is null")
    void shouldThrowExceptionWhenRecensioniIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> product.setRecensioni(null));
        assertEquals("La lista delle recensioni non può essere null", exception.getMessage());
    }

    @Test
    @DisplayName("F2: setRecensioni sets the list when empty")
    void shouldSetRecensioniWhenEmpty() {
        // Arrange
        ArrayList<Recensione> emptyReviewList = new ArrayList<>();

        // Act
        product.setRecensioni(emptyReviewList);

        // Assert
        assertEquals(emptyReviewList, product.getRecensioni());
    }

    @Test
    @DisplayName("F3: setRecensioni sets the list when populated")
    void shouldSetRecensioniWhenPopulated() {
        // Arrange
        ArrayList<Recensione> populatedReviewList = new ArrayList<>();
        Recensione mockReview = mock(Recensione.class);
        populatedReviewList.add(mockReview);

        // Act
        product.setRecensioni(populatedReviewList);

        // Assert
        assertEquals(populatedReviewList, product.getRecensioni());
    }

    // --- setQuantitaProdotto ---

    @ParameterizedTest
    @ValueSource(ints = { 0, 10 })
    @DisplayName("F2, F3: setQuantitaProdotto sets value when valid")
    void shouldSetQuantitaProdottoWhenValid(int validQuantity) {
        // Act
        product.setQuantitaProdotto(validQuantity);

        // Assert
        assertEquals(validQuantity, product.getQuantitaProdotto());
    }

    @Test
    @DisplayName("F1: setQuantitaProdotto throws exception when value is negative")
    void shouldThrowExceptionWhenQuantitaProdottoIsNegative() {
        // Arrange
        int incorrectQuantityValue = -1;

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> product.setQuantitaProdotto(incorrectQuantityValue));
        assertEquals("La quantità del prodotto non può essere negativa", exception.getMessage());
    }

    // --- setPrezzo ---

    @ParameterizedTest
    @ValueSource(doubles = { 0.0, 19.99 })
    @DisplayName("F2, F3: setPrezzo sets value when valid")
    void shouldSetPrezzoWhenValid(double validPrice) {
        // Act
        product.setPrezzo(validPrice);

        // Assert
        assertEquals(validPrice, product.getPrezzo(), 0.001);
    }

    @Test
    @DisplayName("F1: setPrezzo throws exception when value is negative")
    void shouldThrowExceptionWhenPrezzoIsNegative() {
        // Arrange
        double incorrectPriceValue = -1.0;

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> product.setPrezzo(incorrectPriceValue));
        assertEquals("Il prezzo non può essere negativo", exception.getMessage());
    }

    // --- setPeso ---

    @ParameterizedTest
    @ValueSource(doubles = { 0.0, 1.5 })
    @DisplayName("F2, F3: setPeso sets value when valid")
    void shouldSetPesoWhenValid(double validWeight) {
        // Act
        product.setPeso(validWeight);

        // Assert
        assertEquals(validWeight, product.getPeso(), 0.001);
    }

    @Test
    @DisplayName("F1: setPeso throws exception when value is negative")
    void shouldThrowExceptionWhenPesoIsNegative() {
        // Arrange
        double incorrectWeightValue = -0.5;

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> product.setPeso(incorrectWeightValue));
        assertEquals("Il peso non può essere negativo", exception.getMessage());
    }

    // --- setMarca ---

    @ParameterizedTest
    @NullAndEmptySource
    @ValueSource(strings = { "   " })
    @DisplayName("F1, F2, F3: setMarca throws exception for invalid values (null, empty, blank)")
    void shouldThrowExceptionWhenMarcaIsInvalid(String invalidBrand) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> product.setMarca(invalidBrand));
        assertEquals("La marca non può essere null o vuota", exception.getMessage());
    }

    @Test
    @DisplayName("F4: setMarca sets the value when valid")
    void shouldSetMarcaWhenValid() {
        // Arrange
        String validBrand = "Samsung";

        // Act
        product.setMarca(validBrand);

        // Assert
        assertEquals(validBrand, product.getMarca());
    }

    // --- setModello ---

    @ParameterizedTest
    @NullAndEmptySource
    @ValueSource(strings = { "   " })
    @DisplayName("F1, F2, F3: setModello throws exception for invalid values (null, empty, blank)")
    void shouldThrowExceptionWhenModelloIsInvalid(String invalidModel) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> product.setModello(invalidModel));
        assertEquals("Il modello non può essere null o vuoto", exception.getMessage());
    }

    @Test
    @DisplayName("F4: setModello sets the value when valid")
    void shouldSetModelloWhenValid() {
        // Arrange
        String validModel = "Galaxy S10";

        // Act
        product.setModello(validModel);

        // Assert
        assertEquals(validModel, product.getModello());
    }

    // --- setDescrizione ---

    @ParameterizedTest
    @NullAndEmptySource
    @ValueSource(strings = { "   " })
    @DisplayName("F1, F2, F3: setDescrizione throws exception for invalid values (null, empty, blank)")
    void shouldThrowExceptionWhenDescrizioneIsInvalid(String invalidDescription) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> product.setDescrizione(invalidDescription));
        assertEquals("La descrizione non può essere null o vuota", exception.getMessage());
    }

    @Test
    @DisplayName("F4: setDescrizione sets the value when valid")
    void shouldSetDescrizioneWhenValid() {
        // Arrange
        String validDescription = "A high quality product.";

        // Act
        product.setDescrizione(validDescription);

        // Assert
        assertEquals(validDescription, product.getDescrizione());
    }

    // --- setCategoria ---

    @Test
    @DisplayName("F1: setCategoria throws IllegalArgumentException when categoria is null")
    void shouldThrowExceptionWhenCategoriaIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> product.setCategoria(null));
        assertEquals("La categoria non può essere null", exception.getMessage());
    }

    @Test
    @DisplayName("F2: setCategoria sets the value when valid")
    void shouldSetCategoriaWhenValid() {
        // Arrange
        Categoria category = new Categoria();

        // Act
        product.setCategoria(category);

        // Assert
        assertEquals(category, product.getCategoria());
    }

    // --- setId ---

    @ParameterizedTest
    @ValueSource(ints = { -1, 0, 1 })
    @DisplayName("F1, F2, F3: setId sets the value for negative, zero, and positive inputs")
    void shouldSetId(int id) {
        // Act
        product.setId(id);

        // Assert
        assertEquals(id, product.getId());
    }

    // --- setDimensioni ---

    @Test
    @DisplayName("F1: setDimensioni sets value when null")
    void shouldSetDimensioniWhenNull() {
        // Act
        product.setDimensioni(null);

        // Assert
        assertNull(product.getDimensioni());
    }

    @Test
    @DisplayName("F2: setDimensioni sets value when valid string")
    void shouldSetDimensioniWhenValid() {
        // Arrange
        String validDimension = "20x30x10";

        // Act
        product.setDimensioni(validDimension);

        // Assert
        assertEquals(validDimension, product.getDimensioni());
    }

    // --- setImmagine ---

    @Test
    @DisplayName("F1: setImmagine sets value when null")
    void shouldSetImmagineWhenNull() {
        // Act
        product.setImmagine(null);

        // Assert
        assertNull(product.getImmagine());
    }

    @Test
    @DisplayName("F2: setImmagine sets value when valid string")
    void shouldSetImmagineWhenValid() {
        // Arrange
        String validImage = "pic.jpg";

        // Act
        product.setImmagine(validImage);

        // Assert
        assertEquals(validImage, product.getImmagine());
    }
}
