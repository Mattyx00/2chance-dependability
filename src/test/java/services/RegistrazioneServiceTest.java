package services;

import model.beans.Utente;
import model.dao.UtenteDAO;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.NullSource;
import org.junit.jupiter.params.provider.ValueSource;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.MockedStatic;
import org.mockito.junit.jupiter.MockitoExtension;

import java.sql.SQLException;
import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class RegistrazioneServiceTest {

    @Mock
    private UtenteDAO utenteDAO;

    @InjectMocks
    private RegistrazioneService registrazioneService;

    // =================================================================================================
    // Test Data Constants
    // =================================================================================================

    // Valid test credentials
    private static final String TEST_PASSWORD_VALID_COMPLEX = "Pass123!";
    private static final String TEST_PASSWORD_VALID_SIMPLE = "Password123";
    private static final String TEST_PASSWORD_SHORT = "Pass23";

    // Valid test user data
    private static final String TEST_NAME = "Mario";
    private static final String TEST_SURNAME = "Rossi";
    private static final String TEST_EMAIL_PRIMARY = "test@example.com";
    private static final String TEST_EMAIL_SECONDARY = "email@test.com";
    private static final String TEST_EMAIL_NEW = "new@example.com";
    private static final String TEST_EMAIL_DUPLICATE = "duplicate@example.com";
    private static final String TEST_PHONE = "1234567890";
    private static final String TEST_IMAGE_FILENAME = "img.jpg";

    // =================================================================================================
    // Constructor Tests
    // =================================================================================================

    @Test
    @DisplayName("TF1: Should throw exception when UtenteDAO is null")
    void shouldThrowExceptionWhenDaoIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new RegistrazioneService(null));
        assertTrue(exception.getMessage().contains("UtenteDAO cannot be null"));
    }

    @Test
    @DisplayName("TF2: Should instantiate service when UtenteDAO is not null")
    void shouldInitializeWhenDaoIsNotNull() {
        // Act & Assert
        assertNotNull(registrazioneService);
    }

    // =================================================================================================
    // validateAndRegister Tests
    // =================================================================================================

    @Test
    @DisplayName("TF3: Should throw exception when Nome is null")
    void shouldThrowExceptionWhenNomeIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> registrazioneService.validateAndRegister(null, TEST_SURNAME, TEST_PASSWORD_VALID_COMPLEX,
                        TEST_EMAIL_PRIMARY,
                        TEST_PHONE, TEST_IMAGE_FILENAME));
        assertTrue(exception.getMessage().contains("Nome cannot be null"));
    }

    @Test
    @DisplayName("TF4: Should throw exception when Cognome is null")
    void shouldThrowExceptionWhenCognomeIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> registrazioneService.validateAndRegister(TEST_NAME, null, TEST_PASSWORD_VALID_COMPLEX,
                        TEST_EMAIL_PRIMARY,
                        TEST_PHONE, TEST_IMAGE_FILENAME));
        assertTrue(exception.getMessage().contains("Cognome cannot be null"));
    }

    @Test
    @DisplayName("TF5: Should throw exception when Password is null")
    void shouldThrowExceptionWhenPasswordIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> registrazioneService.validateAndRegister(TEST_NAME, TEST_SURNAME, null, TEST_EMAIL_PRIMARY,
                        TEST_PHONE,
                        TEST_IMAGE_FILENAME));
        assertTrue(exception.getMessage().contains("Password cannot be null"));
    }

    @Test
    @DisplayName("TF6: Should throw exception when Email is null")
    void shouldThrowExceptionWhenEmailIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> registrazioneService.validateAndRegister(TEST_NAME, TEST_SURNAME, TEST_PASSWORD_VALID_COMPLEX,
                        null, TEST_PHONE,
                        TEST_IMAGE_FILENAME));
        assertTrue(exception.getMessage().contains("Email cannot be null"));
    }

    @Test
    @DisplayName("TF7: Should throw exception when Telefono is null")
    void shouldThrowExceptionWhenTelefonoIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> registrazioneService.validateAndRegister(TEST_NAME, TEST_SURNAME, TEST_PASSWORD_VALID_COMPLEX,
                        TEST_EMAIL_PRIMARY, null,
                        TEST_IMAGE_FILENAME));
        assertTrue(exception.getMessage().contains("Telefono cannot be null"));
    }

    @Test
    @DisplayName("TF8: Should throw exception when FileName is null")
    void shouldThrowExceptionWhenFileNameIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> registrazioneService.validateAndRegister(TEST_NAME, TEST_SURNAME, TEST_PASSWORD_VALID_COMPLEX,
                        TEST_EMAIL_PRIMARY,
                        TEST_PHONE, null));
        assertTrue(exception.getMessage().contains("FileName cannot be null"));
    }

    @ParameterizedTest
    @DisplayName("TF9, TF10: Should return error when Nome is invalid (Empty or Non-Alphabetic)")
    @ValueSource(strings = { "", "Mario1", "M@rio" })
    void shouldReturnErrorWhenNameIsInvalid(String invalidName) throws SQLException {
        // Arrange
        String validSurname = TEST_SURNAME;
        String validPassword = TEST_PASSWORD_VALID_COMPLEX;
        String validEmail = TEST_EMAIL_PRIMARY;
        String validPhone = TEST_PHONE;
        String validFileName = TEST_IMAGE_FILENAME;

        // Act
        ArrayList<String> errors = registrazioneService.validateAndRegister(
                invalidName,
                validSurname,
                validPassword,
                validEmail,
                validPhone,
                validFileName);

        // Assert
        assertTrue(errors.contains("Errore nome, riprovare"));
    }

    @ParameterizedTest
    @DisplayName("TF11, TF12: Should return error when Surname is invalid (Empty or Non-Alphabetic)")
    @ValueSource(strings = { "", "Rossi1", "R0ssi" })
    void shouldReturnErrorWhenSurnameIsInvalid(String invalidSurname) throws SQLException {
        // Arrange
        String validName = TEST_NAME;
        String validPassword = TEST_PASSWORD_VALID_COMPLEX;
        String validEmail = TEST_EMAIL_PRIMARY;
        String validPhone = TEST_PHONE;
        String validFileName = TEST_IMAGE_FILENAME;

        // Act
        ArrayList<String> arrayErrors = registrazioneService.validateAndRegister(
                validName,
                invalidSurname,
                validPassword,
                validEmail,
                validPhone,
                validFileName);

        // Assert
        assertTrue(arrayErrors.contains("Errore cognome, riprovare"));
    }

    @ParameterizedTest
    @DisplayName("TF13, TF14, TF15: Should return error when Password is invalid (Empty, Short, No Uppercase)")
    @ValueSource(strings = { "", "Pass", "password", "short", "alllowercase123" })
    void shouldReturnErrorWhenPasswordIsInvalid(String invalidPassword) throws SQLException {
        // Arrange
        String validName = TEST_NAME;
        String validSurname = TEST_SURNAME;
        String validEmail = TEST_EMAIL_PRIMARY;
        String validPhone = TEST_PHONE;
        String validFileName = TEST_IMAGE_FILENAME;

        // Act
        ArrayList<String> arrayErrors = registrazioneService.validateAndRegister(
                validName,
                validSurname,
                invalidPassword,
                validEmail,
                validPhone,
                validFileName);

        // Assert
        assertTrue(arrayErrors.contains("Errore password, riprovare"));
    }

    @ParameterizedTest
    @DisplayName("TF16, TF17: Should return error when Email is invalid (Empty or Bad Format)")
    @ValueSource(strings = { "", "mario@", "mario.com", "@domain.com" })
    void shouldReturnErrorWhenEmailIsInvalid(String invalidEmail) throws SQLException {
        // Arrange
        String validName = TEST_NAME;
        String validSurname = TEST_SURNAME;
        String validPassword = TEST_PASSWORD_VALID_COMPLEX;
        String validPhone = TEST_PHONE;
        String validFileName = TEST_IMAGE_FILENAME;

        // Act
        ArrayList<String> arrayErrors = registrazioneService.validateAndRegister(
                validName,
                validSurname,
                validPassword,
                invalidEmail,
                validPhone,
                validFileName);

        // Assert
        assertTrue(arrayErrors.contains("Errore email, riprovare"));
    }

    @Test
    @DisplayName("TF18: Should return error when Email already exists")
    void shouldReturnErrorWhenEmailExisting() throws SQLException {
        // Arrange
        String existingEmail = TEST_EMAIL_DUPLICATE;
        String validName = TEST_NAME;
        String validSurname = TEST_SURNAME;
        String validPassword = TEST_PASSWORD_VALID_COMPLEX;
        String validPhone = TEST_PHONE;
        String validFileName = TEST_IMAGE_FILENAME;

        try (MockedStatic<UtenteDAO> mockedStatic = mockStatic(UtenteDAO.class)) {
            mockedStatic.when(() -> UtenteDAO.isEmailPresent(existingEmail)).thenReturn(true);

            // Act
            ArrayList<String> arrayErrors = registrazioneService.validateAndRegister(
                    validName,
                    validSurname,
                    validPassword,
                    existingEmail,
                    validPhone,
                    validFileName);

            // Assert
            assertTrue(arrayErrors.contains("Email già in utilizzo"));
        }
    }

    @ParameterizedTest
    @DisplayName("TF19, TF20: Should return error when Telefono is invalid (Empty or Not 10 Digits)")
    @ValueSource(strings = { "", "123", "12345678901", "abcdefghij" })
    void shouldReturnErrorWhenTelefonoIsInvalid(String invalidPhone) throws SQLException {
        // Arrange
        String validName = TEST_NAME;
        String validSurname = TEST_SURNAME;
        String validPassword = TEST_PASSWORD_VALID_COMPLEX;
        String validEmail = TEST_EMAIL_PRIMARY;
        String validFileName = TEST_IMAGE_FILENAME;

        // Act
        ArrayList<String> arrayErrors = registrazioneService.validateAndRegister(
                validName,
                validSurname,
                validPassword,
                validEmail,
                invalidPhone,
                validFileName);

        // Assert
        assertTrue(arrayErrors.contains("Errore telefono, riprovare"));
    }

    @Test
    @DisplayName("TF21: Should return multiple errors for multiple invalid fields")
    void shouldReturnMultipleErrors() throws SQLException {
        // Arrange: Invalid Nome and Invalid Password
        String invalidName = "Mario1";
        String invalidPassword = "short";
        String validSurname = TEST_SURNAME;
        String validEmail = TEST_EMAIL_PRIMARY;
        String validPhone = TEST_PHONE;
        String validFileName = TEST_IMAGE_FILENAME;

        // Act
        ArrayList<String> arrayErrors = registrazioneService.validateAndRegister(
                invalidName,
                validSurname,
                invalidPassword,
                validEmail,
                validPhone,
                validFileName);

        // Assert
        assertAll("Verify multiple errors",
                () -> assertTrue(arrayErrors.contains("Errore nome, riprovare")),
                () -> assertTrue(arrayErrors.contains("Errore password, riprovare")));
    }

    @Test
    @DisplayName("TF22: Should register user when all inputs are valid and email is unique")
    void shouldRegisterUserWhenAllInputsValid() throws SQLException {
        // Arrange
        String validEmail = TEST_EMAIL_NEW;
        String validPassword = TEST_PASSWORD_VALID_SIMPLE; // >8 chars, has Upper
        String validName = TEST_NAME;
        String validSurname = TEST_SURNAME;
        String validPhone = TEST_PHONE;
        String validFileName = TEST_IMAGE_FILENAME;

        try (MockedStatic<UtenteDAO> mockedStatic = mockStatic(UtenteDAO.class)) {
            mockedStatic.when(() -> UtenteDAO.isEmailPresent(validEmail)).thenReturn(false);

            when(utenteDAO.addUtente(any(Utente.class))).thenReturn(1);

            // Act
            ArrayList<String> arrayErrors = registrazioneService.validateAndRegister(
                    validName,
                    validSurname,
                    validPassword,
                    validEmail,
                    validPhone,
                    validFileName);

            // Assert
            assertTrue(arrayErrors.isEmpty(), "Error list should be empty on success");

            verify(utenteDAO, times(1)).addUtente(any(Utente.class));
        }
    }

    // =================================================================================================
    // getUserByEmailPassword Tests
    // =================================================================================================

    @Test
    @DisplayName("TF23: Should throw exception when Login Email is null")
    void shouldThrowExceptionWhenLoginEmailIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> registrazioneService.getUserByEmailPassword(null, TEST_PASSWORD_SHORT));
        assertTrue(exception.getMessage().contains("Email cannot be null"));
    }

    @Test
    @DisplayName("TF24: Should throw exception when Login Password is null")
    void shouldThrowExceptionWhenLoginPasswordIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> registrazioneService.getUserByEmailPassword(TEST_EMAIL_SECONDARY, null));
        assertTrue(exception.getMessage().contains("Password cannot be null"));
    }

    @Test
    @DisplayName("TF25: Should delegate to DAO when Login inputs are valid")
    void shouldDelegateToDaoWhenLoginInputsValid() throws SQLException {
        // Arrange
        String validEmail = TEST_EMAIL_SECONDARY;
        String validPassword = TEST_PASSWORD_SHORT;

        Utente expectedUser = new Utente();

        when(utenteDAO.getUserByEmailPassword(validEmail, validPassword)).thenReturn(expectedUser);

        // Act
        Utente user = registrazioneService.getUserByEmailPassword(validEmail, validPassword);

        // Assert
        assertEquals(expectedUser, user);

        verify(utenteDAO).getUserByEmailPassword(validEmail, validPassword);
    }
}
